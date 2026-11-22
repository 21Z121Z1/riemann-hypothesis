import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsPolarizedOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoldsFinite
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDModel

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)

theorem holds_finite {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {χ : HChar E} {k : ℕ} (hk : 0 < k)
    (hχ : χ.OrderDvd k) {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι χ 0 μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      WD.lpOfChar h (ξ.comp a) (ha'.smooth hξ.1) := by
  obtain rfl := eq_loc hξ
  have ho : IsOpen (μ.ker : Set (G E Ω)) :=
    isOpen_ker_of_pow μ hμ hk fun g => DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hχ) g
  have ho2 : IsOpen {g : GK Bw.Kw | μ (Bw.e.symm g : Dec (F := E) A) = 1} :=
    ho.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simp
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  have := nontrivial_B P
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr 1 one_ne_zero 1 one_ne_zero (by simp) (fun _ => 1) (by simp) (by simp)
    ⟨K', hK1⟩ (fun g hg => by
      have : Bw.e g ∈ Subtype.val ⁻¹' U := hK2 hg
      rw [hU'] at this
      have h2 : μ g = 1 := by simpa using this
      simp [h2]) σ
  rw [hL.loc_away (Or.inr rfl) _ _ (ha'.glob art ha σ)] at key
  simpa using key

theorem holds_abs {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {n : (E →+* ℂ) → ℤ}
    {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι (Model.absPow E (1 : ℕ)) n μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      WD.lpOfChar h (ξ.comp a) (ha'.smooth hξ.1) := by
  obtain rfl := eq_loc hξ
  have hμ' := CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at hμ'
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have := nontrivial_B P
  have hcyc : ∀ g : Dec (F := E) A, (μ g : Om l) = algebraMap _ _ (P.χQ (Bw.e g) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g), hμ', cyc_eq_map_cycZ]
    rfl
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr (tInv P) (fun h0 => by simpa [h0] using tInv_mul P) (l : ℚ_[l])⁻¹
    (inv_ne_zero hl) (by rw [eq_inv_smul_iff₀ hl, smul_phiB_tInv]) (fun g => P.χQ g) (fun g => Units.ne_zero _)
    (smul_actQ_tInv P) Bw.Kw (fun g _ => hcyc g) σ
  have h2 : (μ σ : Om l) = algebraMap _ _ (P.χQ (weilToGK Bw h σ) : ℚ_[l]) := hcyc ⟨σ, Weil_le_Dec h σ.2⟩
  rw [h2, ← map_mul, mul_inv_cancel_left₀ (Units.ne_zero _), inv_zpow', neg_neg, map_zpow₀, map_zpow₀, map_natCast,
    map_natCast, alpha, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow (hj.mem_placesOver h)] at key
  convert key using 1
  have hu := (Model.absPow_isAbsPow E (1 : ℕ)).1 w
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  set χ := Model.absPow E (1 : ℕ)
  have e1 : ∀ x, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, GlobalTheory.SmGL.SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  rw [MonoidHom.comp_apply, e1, ha'.ord_eq, Units.val_zpow_eq_zpow_val, hval]
  simp [Complex.cpow_neg, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

omit P Bw h hj in

theorem hypotheses_met (hA : GlobalArtinReciprocity) (hL : LocalLanglandsGL) (hw : w ∈ placesOver E l) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧ ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ ∧
      ∃ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (LL : FinExt l)
        (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
        (∃ ξ, GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ) ∧ ∃ a, IsLocalArtin h a := by
  obtain ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, rc, a, ha', -⟩ :=
    ParamAboveModel.hypotheses_met (Ω := Ω) ι hA hL hw
  exact ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, a, ha'⟩

end GlobalTheory.Published.CharWDModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotCompatCyc
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGlobAll.Model

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}

def Compat (π : CuspSub E a) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous R ∧ IsSSRep R ∧
    (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
        IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
          wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

theorem compat_of (H : GlobalTheory.Published.CaraianiLocalGlobal) (ha : 2 ≤ a) (π : CuspSub E a) (hc : π.IsCsd)
    (hcoh : GKCoh.IsCohomological π) : ∃ R, Compat Ω ι π R := H E Ω l ι a ha π hc hcoh

omit [IsCMField E] [IsAlgClosure E Ω] [NumberField E] in

theorem isPstAt_one {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) :
    IsPstAt P Bw (1 : ↥Gw →* GL (Fin a) (Om l)) := by
  refine ⟨Bw.LL, 1, isModel_one Bw, ?_⟩
  have := Bw.LL.2
  let b := Module.finBasis ℚ_[l] (Fin a → ↥Bw.LL.1)
  refine GlobalTheory.PstExt.isPst_of_coord P (LL := ℚ_[l]) (ρ := (1 : Representation ℚ_[l] ↥(GK Bw.Kw) ℚ_[l]))
    (E := b.equivFun) (fun g x i => ?_)
    (isPst_one_of_kummer l P (GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T) _)
  have : Bw.repE Bw.LL (1 : ↥Gw →* GL (Fin a) ↥Bw.LL.1) g x = x := by simp [LocBridge.repE]
  rw [this]; rfl

theorem rec_triv {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (hσ : (CuspSub.triv E le_rfl).IsLocComp w σ) : rc (algNorm σ) = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
  rw [rec_algNorm hrc]
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  have h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
    simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
  rw [GlobalTheory.GalOfCusp.Model.locComp_triv hσ h1, H.one]
  have e : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
  rw [e, WD.lpTw_zero]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  ext i; simp [WDRep.ofChars]

theorem compat_triv : Compat Ω ι (CuspSub.triv E (le_refl 1)) 1 := by
  refine ⟨continuous_const, fun W _ => let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩,
    fun w hl A h rc hrc σ hσ => ?_, fun P AI ⟨T⟩ w A h O _ _ _ Bw hj => ?_⟩
  · rw [rec_triv Ω hrc hσ]; exact GlobalTheory.GalOfCusp.Model.isWDOf_one hl h ι
  have hp : IsPstAt P Bw ((1 : G E Ω →* GL (Fin 1) (Qbar l)).comp (Dec (F := E) A).subtype) := isPstAt_one Ω T Bw
  refine ⟨hp, fun σ hσ rc hrc => ?_⟩
  rw [rec_triv Ω hrc hσ]
  have e : (1 : G E Ω →* GL (Fin 1) (Qbar l)) = GlobalTheory.TripleGal.rk1 (1 : G E Ω →* (Qbar l)ˣ) := by
    ext g i j; simp [GlobalTheory.TripleGal.rk1]
  have := nontrivial_B P
  have hs : WeilDeligne.IsSmooth (1 : Weil h →* ℂˣ) := .of_trivial fun _ => rfl
  rw [GlobalTheory.Published.ParamAboveModel.eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) 1 hs fun σ => ?_]
  · refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
    ext i; simp [WDRep.ofChars]
  · rw [e] at hp ⊢
    have key := GlobalTheory.Published.ParamAboveModel.mem_eig_wdAt P ι Bw h hj 1 hp 1 one_ne_zero 1 one_ne_zero (by simp)
      (fun _ => 1) (by simp) (by simp) Bw.Kw (fun g _ => by simp) σ
    simpa using key

theorem not_compat_cyc (hL : GlobalTheory.Published.LocalLanglandsGL) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    ¬ Compat Ω ι (CuspSub.triv E (le_refl 1)) ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l)) := by
  rintro ⟨-, -, H, -⟩
  obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w h
  have h2 : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _) :=
    ⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩,
      fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))),
      fun _ _ => rfl⟩
  have h3 := (H w hl A h rc hrc _ h2).wdOf_eq hl
  rw [rec_triv Ω hrc h2, wdOf_cyc] at h3
  have h4 := congrArg (fun x : WD h => x.charPol (frob h)) h3
  simp only [WD.lpTw_mk, WD.charPol_mk] at h4
  have e1 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ (frob h) = 1 := by ext; simp
  rw [WDRep.tw_ρ, e1, deg_frob] at h4
  have h5 := LinearMap.aeval_self_charpoly ((((normV w : ℕ) : ℂ) ^ (((1 : ℝ) : ℝ) : ℂ)) ^ (1 : ℤ) •
    (1 : Module.End ℂ (Fin 1 → ℂ)))
  rw [h4, LinearMap.charpoly_one] at h5
  have h6 := congrFun (LinearMap.congr_fun h5 fun _ => 1) 0
  simp [sub_eq_zero] at h6
  exact (one_lt_normV w).ne' h6

variable {Ω ι}

theorem Compat.unram_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    (∀ g ∈ Ine (F := E) A, R g = 1) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  have h1 := H.2.2.1 w hl A h rc hrc σ hσ
  obtain ⟨N, hN⟩ := (exists_isWDOf_iff hl (isTameChar_tameL h hl)).1 ⟨_, h1⟩
  rw [← hN.unr_wdOf_iff hl (isTameChar_tameL h hl) ι, h1.wdOf_eq hl]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

theorem Compat.crys_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    IsCrysAt P Bw (R.comp (Dec (F := E) A).subtype) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  obtain ⟨h1, h2⟩ := H.2.2.2 P AI ⟨T⟩ w A h O Bw hj
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff (h := h) (hj := hj) (ι := ι) (hr := h1), h2 σ hσ rc hrc]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

end GlobalTheory.LocGlobAll.Model

end
end

