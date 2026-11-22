import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_baseLevel_iff_finiteGroup_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ↔ g0 ∈ P.H := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
    rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H) ↔ _
  rw [e]
  exact ⟨fun hk => hk.2.2, fun hg => ⟨hl.1, hl.2.1, hg⟩⟩

theorem baseLevelCharacter_eq_blockCharacter_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hg : g0 ∈ P.H) :
    levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = ((P.chi ⟨g0, hg⟩ : ℂˣ) : ℂ) := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  have e2 : levFn (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) := by
    show ext1 P.H P.chi _ * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ = _
    simp
  unfold levChi
  rw [e2, e, extendOne_of_mem _ hg]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_triv (R : RealDat D A Ks) (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ = 1 := by
  unfold levChi
  show ((ext1 (⊤ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊤ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
    (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
  unfold ext1
  split_ifs <;> simp

theorem hasType_flag1 (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (F : GA D (Yc D 0) → ℂ)
    (hF : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P), ∀ g, F (g * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k * F g) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F := by
  intro κ hκ g
  have h1 : κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))) := hκ
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h1.2.2
  have hJ : κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) := by
    show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H)
    rw [e]
    exact ⟨h1.1, h1.2.1, P.H.one_mem⟩
  have c1 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = 1 := by
    unfold levChi
    show ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    rw [e]
    have h2 : ext1 P.H (⇑P.chi) (1 : G0 R.Pg D.R.r) = 1 := blockDiagonalExtendByOnePrimeField_one P.H P.chi
    erw [h2]
    simp
  have c2 : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) κ = 1 := by
    unfold levChi
    show ((ext1 (⊥ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊥ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    unfold ext1
    split_ifs <;> simp
  rw [hF κ hJ g, c1, c2]

theorem mult_act_of_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)),
      ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
        (T : MMap (MP R)) v (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 ((T : MMap (MP R)) v) g := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    intro v g
    have hF := hasType_flag1 R P (T v) (fun k hk g' => hT.lev v k hk g')
    have := level_action_spec hF ⟨κ, hl⟩ κ hl g
    show T v (g * κ) = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T v) g
    rw [this, levChi_flag_triv, inv_one, one_mul]
  | zero =>
    intro v g
    show (0 : GA D (Yc D 0) → ℂ) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (0 : GA D (Yc D 0) → ℂ) g
    rw [map_zero]
    rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro v g
    show (T₁ v + T₂ v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T₁ v + T₂ v) g
    rw [map_add, Pi.add_apply, Pi.add_apply, h₁ v g, h₂ v g]
  | smul a T _ hT =>
    intro v g
    show (a • T v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (a • T v) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hT v g]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem isRedHom_conj {D : D7} {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (c : G0g D.nd) (hred : IsRedHom X red)
    (hf : FixRed X (fun k => c⁻¹ * red k * c) b') : IsRedHom X (fun k => c⁻¹ * red k * c) := by
  refine ⟨goodAt_of_fixRed hf, fun k hk k' hk' => ?_, fun γ => ?_, fun k hk => ?_⟩
  · simp only [hred.2.1 k hk k' hk', mul_assoc, mul_inv_cancel_left]
  · obtain ⟨k, hk, e⟩ := hred.2.2.1 (c * γ * c⁻¹)
    exact ⟨k, hk, by simp only [e]; group⟩
  · rw [← hred.2.2.2 k hk]
    show c⁻¹ * red k * c = 1 ↔ red k = 1
    constructor
    · intro e
      calc red k = c * (c⁻¹ * red k * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e; rw [e]; group

theorem seeAt_exists : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h hι hL hlev hpin hE
  obtain ⟨eR, plg, iso, hpl, he, hdiv, heG⟩ := hpin
  obtain ⟨ψ0, hgen, -, π, hπ, hmem, hchi⟩ := hlev
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    intro kv
    have := D.naut.plGw_over kv.1 kv.2
    simp [placesOver] at this
    exact this
  obtain ⟨t₀, ht₀, red, b, hred, hfix, hlift, hcover⟩ := GlobalTheory.Mem.SRe.TrPt.exists_trans D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG
  obtain ⟨c, hc⟩ := GlobalTheory.T.conj_level_conjCharacter_symmetricLevel D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG ψ0 hgen π hπ red b hred hfix hgw
  obtain ⟨b', hfix'⟩ := GlobalTheory.T.isFixedBasisReductionMap_conj D X red b c hgw hfix
  obtain ⟨kc, hkc, hkcv⟩ := hred.2.2.1 c
  have hK : ∀ x, x ∈ X.B.I.Kset ↔ x ∈ GlobalTheory.RowLev.Inhab.Ksub X.B.I := fun x => Iff.rfl
  have hmul := hred.2.1
  have red_one : red 1 = 1 := by
    have e := hmul 1 ((hK 1).2 (Subgroup.one_mem _)) 1 ((hK 1).2 (Subgroup.one_mem _))
    rw [mul_one] at e
    exact left_eq_mul.mp e
  have red_inv : ∀ x ∈ X.B.I.Kset, red x⁻¹ = (red x)⁻¹ := by
    intro x hx
    have hx' : x⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK x).1 hx))
    have e := hmul x⁻¹ hx' x hx
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have memK : ∀ k ∈ X.B.I.Kset, kc⁻¹ * k * kc ∈ X.B.I.Kset := fun k hk =>
    (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hK _).1 hkc)) ((hK _).1 hk)) ((hK _).1 hkc))
  have red_conj : ∀ k ∈ X.B.I.Kset, red (kc⁻¹ * k * kc) = c⁻¹ * red k * c := by
    intro k hk
    have hkc' : kc⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK _).1 hkc))
    have h1 : kc⁻¹ * k ∈ X.B.I.Kset := (hK _).2 (Subgroup.mul_mem _ ((hK _).1 hkc') ((hK _).1 hk))
    rw [hmul _ h1 _ hkc, hmul _ hkc' _ hk, red_inv _ hkc, hkcv]
  obtain ⟨t, ht⟩ : ∃ t : GA D (D.sp.Y 0), t = (iotaX X h).symm (1, kc) * t₀ := ⟨_, rfl⟩
  have hkap : ∀ k, kap X h t k = kap X h t₀ (kc⁻¹ * k * kc) := by
    intro k
    have e : ((1 : X.B.I.Ginf), kc⁻¹ * k * kc) = ((1, kc) : X.B.I.GA)⁻¹ * (1, k) * (1, kc) := by
      ext <;> simp
    show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) =
      t₀⁻¹ * (iotaX X h).symm (1, kc⁻¹ * k * kc) * t₀
    rw [e, map_mul, map_mul, map_inv, ht]
    group
  set red' : X.B.I.Gf → G0g D.nd := fun k => c⁻¹ * red k * c with hred'def
  have hred' : IsRedHom X red' := isRedHom_conj c hred hfix'
  have hliftT : ∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red' k))) (kap X h t k) := by
    intro k hk
    rw [hkap, hred'def]
    simp only
    rw [← red_conj k hk]
    exact hlift _ (memK k hk)
  have key : ∀ k ∈ X.B.I.Kset, (kap X h t k ∈ JR R F ↔ k ∈ X.K2) ∧
      ∀ hJ : kap X h t k ∈ JR R F, chiR R F (kap X h t k) = star (X.chi2 k) := by
    intro k hk
    have hl := hliftT k hk
    have hiff := mem_baseLevel_iff_finiteGroup_lift R (R.levR F true) hl
    have hc1 := (hc k hk).1
    refine ⟨?_, fun hJ => ?_⟩
    · rw [show kap X h t k ∈ JR R F ↔ _ from hiff, hmem, hc1]
    · have hg : R.eG (eR.symm (red' k)) ∈ (R.levR F true).H := hiff.1 hJ
      have hg' : reord π (R.eG (eR.symm (red' k))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H := (hmem _).1 hg
      show levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = _
      rw [baseLevelCharacter_eq_blockCharacter_lift R (R.levR F true) hl hg, hchi _ hg hg']
      exact (hc k hk).2 hg'
  have hio : ∀ k, iotaX X h ((iotaX X h).symm (1, k)) = (1, k) := fun k => (iotaX X h).apply_symm_apply _
  have hconjEq : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ = (iotaX X h).symm (1, k) := by
    intro k
    group
  have hK2K : ∀ k ∈ X.K2, k ∈ X.B.I.Kset := fun k hk => hk.1
  refine ⟨t, ⟨?_, ?_, eR.symm, red', ?_, ⟨hred', ?_⟩, ?_⟩⟩
  · have e : t = t₀ * (t₀⁻¹ * (iotaX X h).symm (1, kc) * t₀) := by rw [ht]; group
    rw [e]
    exact Subgroup.mul_mem _ ht₀ (hlift kc hkc).1
  · intro y
    have hJ' : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X ↔ k ∈ X.K2 := by
      intro k
      rw [hconjEq, Set.mem_preimage, hio]
      exact ⟨fun hh => hh.2, fun hh => ⟨rfl, hh⟩⟩
    have hy : y ∈ JR R F ∨ (t⁻¹)⁻¹ * y * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X → ∃ k ∈ X.B.I.Kset, y = kap X h t k := by
      rintro (hy | hy)
      · have hyF : y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := ⟨hy.1, hy.2.1, Subgroup.mem_top _⟩
        obtain ⟨k', hk', e⟩ := hcover y hyF
        refine ⟨kc * k' * kc⁻¹, (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hK _).1 hkc) ((hK _).1 hk'))
          (Subgroup.inv_mem _ ((hK _).1 hkc))), ?_⟩
        rw [hkap, e]
        congr 1
        group
      · have h2 : (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).1 = 1 ∧ (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2 ∈ X.K2 := hy
        refine ⟨(iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2, h2.2.1, ?_⟩
        have e : (iotaX X h).symm (1, (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2) = (t⁻¹)⁻¹ * y * t⁻¹ := by
          rw [← h2.1]
          exact (iotaX X h).symm_apply_apply _
        show y = (t⁻¹ * (iotaX X h).symm (1, _) * t : GA D (D.sp.Y 0))
        rw [e]
        group
    refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      exact (hJ' k).2 ((key k hk).1.1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inr h1)
      exact (key k hk).1.2 ((hJ' k).1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      rw [(key k hk).2 h1]
      show adelicCharacterOfHidaSetting X (iotaX X h ((t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹)) = _
      rw [hconjEq, hio]
      rfl
  · intro k hk
    have hkK := hK2K k hk
    have hJ := (key k hkK).1.2 hk
    exact ⟨hJ, (key k hkK).2 hJ⟩
  · intro k hk T hT v g
    exact mult_act_of_lift R (R.levR F true) (hliftT k hk) T hT v g
  · intro γ
    show star (D.ntypes.e0.coeff γ) = D.what₂.embLL ((idemOf A.X).coeff (eR.symm γ))
    rw [he, MulEquiv.apply_symm_apply, hE γ]

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mv

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

def sameGrp {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e k := (by with_unfolding_all exact ((plEquiv a.N.naut b.N.naut k) :))
  pl k v := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv h h' k v) :))
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by with_unfolding_all exact ((alg b z.alg) :))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

theorem levOf_tr {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) : LevOf b.st I U (levCh b L) := by
  constructor
  case is => exact (by with_unfolding_all exact ((levIs_tr b h.is) :))
  case C => exact (by with_unfolding_all exact ((congrArg (chFr b) h.C) :))
  case xiH => exact (by with_unfolding_all exact (h.xiH :))
  case Pg => exact (by with_unfolding_all exact (h.Pg :))
  case Q => exact (by with_unfolding_all exact (h.Q :))
  case beta => exact (by with_unfolding_all exact (h.beta :))

theorem goodSet_tr (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : (fun g => a.D.ntypes.e0.coeff (eR g)) = fun g => b.D.ntypes.e0.coeff ((eR.trans s.iso) g) :=
    funext fun g => (s.e0 (eR g)).symm
  refine (goodSet_iff b.st (px := px) _ Xg).2 ?_
  tr_via (fun c : Gc B px → ℂ => (∀ χ : Gc B px → B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
    ∑ g : Gc B px, c g * B.embLL (χ g) = B.embLL (χ 1)) ∧ ∀ g, B.embLL ((idemOf Xg).coeff g) = c g) e
    ((goodSet_iff a.st (px := px) eR Xg).1 h)

def cpDat (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((alg b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := cpR b z)
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    (lev := (by with_unfolding_all exact ((levOf_tr b z.lev) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((goodSet_tr b s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

theorem lawsCore_tr {K : Formalism.L2.Pj.Core a.D} (h : Formalism.L2.Pj.LawsCore K) : Formalism.L2.Pj.LawsCore (core b K) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cuspMul => exact (by with_unfolding_all exact (h.cuspMul :))
  case latZ => exact (by with_unfolding_all exact (h.latZ :))
  case cuNe => exact (by with_unfolding_all exact (h.cuNe :))
  case expo => exact (by with_unfolding_all exact (h.expo :))

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem cp_holds (h : Holds z.R z.F) : Holds (cpDat b s z).R (cpDat b s z).F := (by with_unfolding_all exact ((holds_tr b (iK := z.alg) h) :))

theorem cp_exAt (h : z.R.toRealDat.ExAt) : (cpDat b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem cp_inGeo (h : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (cpDat b s z).geo := (by with_unfolding_all exact ((inGeo_tr b (iK := z.alg) h) :))

theorem cp_canon (h : z.core.Q.Canon) : (cpDat b s z).core.Q.Canon := (by with_unfolding_all exact (h :))

theorem forcedContentPlaces_eq_transport_sameFiniteGroup (F0) : (cpDat b s z).W1 F0 = z.W1 ((F0)) :=
  (by with_unfolding_all exact ((congrArg (fun X : Cx.CxData (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).fam3.amb3 =>
    {w : B.places.Pl | ∃ j, ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
    (X.data z.F.cr false).Iw j (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
              (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
        (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ ((F0) : HeightOneSpectrum (𝓞 a.D.what₂.LL) → Fin a.D.R.m → ℝ) w' j ≠ 0})
    (toCx3_eq b (iK := z.alg) z.R z.F).symm) : _))

section Read

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def fixTup {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : HdB b R :=
  letI := alg b iK
  { y' with tup := (by with_unfolding_all exact (y.tup :)), tupT := (by with_unfolding_all exact (y.tupT :)), tupT_tup := (by with_unfolding_all exact (y.tupT_tup :)), tup0 := (by with_unfolding_all exact (y.tup0 :)) }

theorem fixTup_same {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} {y : Hd R} {y' : HdB b R} (h : Same b y y') :
    Same b y (fixTup b y y') :=
  ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact (h.PY :)), (by with_unfolding_all exact (h.PW :))⟩

variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat)
  (y' : HdB b R.toRealDat)

def hd3 : letI := alg b iK; Hd (real3 b R).toRealDat := (by with_unfolding_all exact ((fixTup b y y') :))

def mCp (mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G) : Bool → b.D.what₂.Tup → Mat1 b.D.what₂.LL G := (by with_unfolding_all exact (mA :))

def pCp (p : PkD a.D G) : PkD b.D G := (by with_unfolding_all exact (p :))

theorem dall_tr {n : ℕ} (h : n = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
    (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))))) : letI := alg b iK
    n = Module.finrank ℂ (Mult.Mult (real3 b R).θ ((real3 b R).MY 0)
      (levS _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))
      (levChi _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))) := by
  tr_via (fun m : type_of% (@Mult.Mult a.D) => n = Module.finrank ℂ (m R.θ (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))))
    (mult_eq b a) h

set_option maxHeartbeats 1000000 in

theorem pkT_tr (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.T.chainComparison_transfer_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Read

set_option maxHeartbeats 1000000 in

theorem exists_moved : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Holds z₀.R z₀.F →
    z₀.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z₀.geo → GrpTrue Z₀.N f → o.Fits → ∃ m : Moved o, m.Copy ∧ m.Coh := by
  intro B f T w Z₀ hX Wt z₀ q o h1 h2 h3 h4 h5
  have s : SameGrp (B := B) (C := w.C) Z₀ o.Z := sameGrp o.Z h4 h5.grp
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C Z₀ o.Z _ _ _ _ _ _ _ _ z₀.alg _ z₀.R.toRealDat q.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_tr (a := Z₀) o.Z (iK := z₀.alg) z₀.F q.y y' hy q.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C Z₀ o.Z _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).1
  letI : Algebra z₀.core.Q.c.F (Late.D o.Z).what₂.LL := alg (a := Z₀) o.Z z₀.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% q.t.tA) = q.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hs := fixTup_same (a := Z₀) o.Z (iK := z₀.alg) hy
  refine ⟨{ z := cpDat (a := Z₀) o.Z s z₀
            intersectionNumber_baseChange := cp_holds (a := Z₀) o.Z s z₀ h1
            exAt := cp_exAt (a := Z₀) o.Z s z₀ h2
            inGeo := cp_inGeo (a := Z₀) o.Z s z₀ h3
            Xg := rfl
            tr := rfl
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := Z₀) o.Z h.1) :)), cp_canon (a := Z₀) o.Z s z₀ h.2.1, (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩
            eta := (by with_unfolding_all exact (he :))
            W1 := (by with_unfolding_all exact ((forcedContentPlaces_eq_transport_sameFiniteGroup (a := Z₀) o.Z s z₀) :))
            y := (by with_unfolding_all exact ((hd3 (a := Z₀) o.Z (iK := z₀.alg) q.y y') :))
            tup := (by with_unfolding_all exact (q.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((heq_of_eq (congrArg (fun r : type_of% q.t.tA => (r c ((u))).j) hA)) : _)) }, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := Z₀) o.Z z₀.core)) :))
  · exact (by with_unfolding_all exact ((HEq.refl (real3 (a := Z₀) o.Z (iK := z₀.alg) z₀.R)) :))
  · exact (by with_unfolding_all exact ((HEq.refl q.y.tupT) :))
  · exact (by with_unfolding_all exact (hy.PY :))
  · exact (by with_unfolding_all exact (hy.PW :))
  · exact (by with_unfolding_all exact (a2 :))
  · exact (by with_unfolding_all exact (a3 :))
  · exact (by with_unfolding_all exact (a4 :))
  · exact (by with_unfolding_all exact (a5 :))
  · exact (by with_unfolding_all exact (a6 :))
  · exact (by with_unfolding_all exact (a7 :))

end GlobalTheory.Mem.R3.Rw.Mv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

theorem readPk_pin_exists : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ (s : Side0 o) (r : ReadPk m s), r.Pin := by
  intro B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_side_reading_level_zero_moved B f T w Z₀ hX Wt z₀ q o hIn hF m
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := GlobalTheory.T.exists_reading_in_movedRowData B f T w Z₀ hX Wt z₀ q o hIn hF m s
  obtain ⟨Z⟩ := hs Y h2 h9 h10 h11
  exact ⟨s, ⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11, h12⟩⟩

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMemChartLevelIffReductionFixesTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_mem_chartLevel_iff_reduction_fixes_typePrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ x, x ∈ F.levJ.Uloc v → (rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.U ↔ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  first | exact @GlobalTheory.Mem.Col2.TC.typeRead_core | exact GlobalTheory.Mem.Col2.TC.typeRead_core | (intros; apply GlobalTheory.Mem.Col2.TC.typeRead_core <;> assumption)
end

