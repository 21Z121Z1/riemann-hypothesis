import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.MonodromyFreeOfNoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoLink (x : GL (Fin n) (Qbar l)) (Q : ℕ) : Prop :=
  ∀ α β : Qbar l, (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α → (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β →
    ∀ k : ℕ, 1 ≤ k → α ^ k ≠ ((Q : Qbar l) * β) ^ k

def UnlinkAt (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) : Prop :=
  ∃ (s : G F Ω) (j : ℕ), 1 ≤ j ∧ IsFrob A (normV w ^ j) s ∧ NoLink (r s) (normV w ^ j)

def Unlinked (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite → UnlinkAt r w A

def Wit [IsCMField F] (_ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Unlinked r

omit [NumberField F] in

def WitQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

def AutPol [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π

def AutCsd0 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π

omit [NumberField F] in

def IsAutomorphicOverImagQuad (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π

def IsAutCsdN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → Wit ι r)

omit [NumberField F] in

def IsAutQN (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      (∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π) ∧
        Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem mkCsd [IsCMField F] (h : AutCsd0 ι r) (_ : Continuous r → Wit ι r) : IsAutCsd ι r := h
theorem mkCsd' [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → Wit ι r) : IsAutCsdN ι r := ⟨h, u⟩
theorem csd0 [IsCMField F] (h : IsAutCsd ι r) : AutCsd0 ι r := h
theorem csd0' [IsCMField F] (h : IsAutCsdN ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem automorphicQ_of_witness (h : IsAutQ ι r) : IsAutomorphicOverImagQuad ι r := h
omit [NumberField F] in
theorem autQ0' (h : IsAutQN ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem mkQ (h : IsAutomorphicOverImagQuad ι r) (_ : Continuous r → WitQ ι r) : IsAutQ ι r := h
omit [NumberField F] in
theorem mkQ' (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → WitQ ι r) : IsAutQN ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩

theorem UnlinkAt.unlAt {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : UnlinkAt r w A) : UnlAt ι r w A := by
  obtain ⟨s, j, hj, hs, hn⟩ := h
  refine ⟨s, j, hj, hs, fun α hα hβ => ?_⟩
  have back : ∀ z : ℂ, ((r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot z →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot (ι.symm z) := fun z hz => by
    rw [← ι.apply_symm_apply z] at hz
    exact (Polynomial.isRoot_map_iff (f := ι.toRingHom) ι.injective).1 hz
  refine hn _ _ (back _ hβ) (back _ hα) 1 le_rfl ?_
  simp
end Conv

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwV (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwV.refl (x : WD h) : AwV x x := ⟨fun _ => rfl, fun _ => rfl⟩
theorem AwV.of_aw {x y : WD h} (k : Aw x y) : AwV x y := ⟨k.pol, k.n0⟩

theorem charPol_sum (x y : WD h) (g : ↥(Weil h)) : (x.lpSum y).charPol g = x.charPol g * y.charPol g := by
  rw [← WD.inePol_of_mem _ g.2, WD.inePol_sum, WD.inePol_of_mem _ g.2, WD.inePol_of_mem _ g.2]

theorem AwV.sum {x y x' y' : WD h} (k : AwV x y) (k' : AwV x' y') : AwV (x.lpSum x') (y.lpSum y') :=
  ⟨fun g => by rw [charPol_sum, charPol_sum, k.pol, k'.pol],
    fun m => by rw [k.n0 ((WD.monomial_sum_iff _ _).1 m).1, k'.n0 ((WD.monomial_sum_iff _ _).1 m).2]⟩

theorem AwV.tw {x y : WD h} (k : AwV x y) (s : ℝ) : AwV (x.lpTw s) (y.lpTw s) :=
  ⟨fun g => GlobalTheory.GalCut.AwayMono.charPol_lpTw_congr k.pol s g, fun m => by rw [k.n0 ((WD.monomial_twist_iff _ _).1 m)]⟩

theorem AwV.eq_of_noRatio {x y : WD h} (k : AwV x y) {g : ↥(Weil h)} (hx : NoRatio x g) : x = y :=
  k.n0 (monodromyFree_of_noRatio (g := g) (by simpa only [NoRatio, WD.eig, k.pol] using hx))

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

def WDN (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := ∃ x : WD h, IsWDOf ι r x ∧ AwV x y

variable {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDN.of_isWDOf (k : IsWDOf ι r y) : WDN ι r y := ⟨y, k, .refl y⟩
theorem WDN.isWDOf (k : WDN ι r y) (m : y.mono0) : IsWDOf ι r y := by
  obtain ⟨x, hx, k⟩ := k
  exact k.n0 m ▸ hx
theorem WDN.of_unr (k : WDN ι r y) (m : y.unr) : IsWDOf ι r y := k.isWDOf (WD.unr_mono0 _ m)
theorem WDN.of_hasSat {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {a : ℕ}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (k : WDN ι r (rc (algNorm σ))) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := k.of_unr (unr_algNorm hrc σ S hS)
theorem WDN.of_conj (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDN ι r' y := by
  obtain ⟨x, hx, k⟩ := k
  exact ⟨x, hx.of_conj hl P hP, k⟩
theorem WDN.awV (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : AwV (wdOf h hl ι r) y := by
  obtain ⟨x, hx, k⟩ := k
  rwa [hx.wdOf_eq hl]
theorem WDN.of_aw (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hc : Continuous r) (k : AwV (wdOf h hl ι r) y) : WDN ι r y :=
  ⟨_, isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp hc), k⟩
end Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def ParAtN {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (p : Gu.Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 F) ∉ w.asIdeal → WDN ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (p A h rc)

def LocGlobN (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 F) ∉ w.asIdeal → WDN ι r (rc (algNorm σ))) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (rc (algNorm σ))

def CsdSsN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            Lev.SsCmp (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

def CsdMonoOddN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → Odd a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)).mono0 → (rc (algNorm σ)).mono0

def CarV : Prop := CarU ∧ CsdSsN ∧ CsdMonoOddN

theorem ssN (H : Lev.CsdSs) : CsdSsN := fun E Ω _ _ _ _ _ _ l _ ι a ha π hd hc => by
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha π hd hc
  exact ⟨R, h1, h2, fun w hw A h rc hrc σ hσ => .of_isWDOf (h3 w hw A h rc hrc σ hσ), h4⟩
theorem ssN' (H : CsdSsN) : CsdSsN := H
theorem monoN (H : Lev.CsdMonoOdd) : CsdMonoOddN := fun E Ω _ _ _ _ _ _ l _ ι a ha ho π hd hc => by
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha ho π hd hc
  exact ⟨R, h1, h2, fun w hw A h rc hrc σ hσ => .of_isWDOf (h3 w hw A h rc hrc σ hσ), h4⟩
theorem monoN' (H : CsdMonoOddN) : CsdMonoOddN := H
theorem ss_of_carV (H : CarV) : CsdSsN := H.2.1
theorem mono_of_carV (H : CarV) : CsdMonoOddN := H.2.2
theorem bridgeV : GlobalTheory.Published.GelfandKazhdanDual → (CarV → CarU) ∧ (PairU → CuspU) :=
  fun hGK => ⟨And.left, (UpperTheory.GalN.bridge' hGK).2⟩
theorem ofDualV (_ : GlobalTheory.Published.GelfandKazhdanDual) (h : CarV) : CarU := h.1

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.LocLanglands GlobalTheory.LocGL UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

private theorem norm_inf {F : Type} [Field F] [NumberField F] (χ : HChar F) (k : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 ∨ ordF v k = 0) : ‖((χ.inf k : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  have e := (χ ^ N).val_principal ∅ (fun v _ => hu v) k
  have h1 : ‖((∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ (∅ : Finset _)), (χ ^ N).val v ^ ordF v k : ℂˣ) : ℂ)‖ = 1 := by
    refine finprod_induction (fun z : ℂˣ => ‖(z : ℂ)‖ = 1) (by simp) (fun x y hx hy => by simp [hx, hy]) fun v => ?_
    have e2 : (χ ^ N).val v = χ.val v ^ N := rfl
    rcases h v with h | h
    · simp [e2, h]
    · simp [h]
  have e2 : (χ ^ N).inf k = χ.inf k ^ N := rfl
  rw [e, Finset.prod_empty, mul_one, e2] at h1
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow, inv_eq_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem type_zero_window {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ)
    (ha : IsAlgPos χ a) (v : HeightOneSpectrum (𝓞 F)) (h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ < (normV v : ℝ))
    (h2 : 1 < (normV v : ℝ) * ‖((χ.val v : ℂˣ) : ℂ)‖) : a = 0 := by
  obtain ⟨s, hs⟩ := GlobalTheory.HeckeNormPow.norm_val_eq_rpow F χ
  obtain ⟨φ₀⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hpar : ∀ φ, a φ = a φ₀ := fun φ => UpperTheory.heckeChar_parallel_weight _ _ _ ha φ φ₀
  obtain ⟨-, n2, n3⟩ := Model.absPow_isAbsPow F s
  have hq : ∀ u : HeightOneSpectrum (𝓞 F), (1 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := fun u => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm u
  have k := norm_inf (χ * Model.absPow F s) (Units.mk0 (2 : F) two_ne_zero) fun u => Or.inl (by
    rw [HChar.val_mul, Units.val_mul, norm_mul, hs, n2, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (zero_lt_one.trans (hq u))),
      ← Real.rpow_add (zero_lt_one.trans (hq u))]
    simp)
  have e0 : (χ * Model.absPow F s).inf (Units.mk0 (2 : F) two_ne_zero) =
    χ.inf (Units.mk0 (2 : F) two_ne_zero) * (Model.absPow F s).inf (Units.mk0 (2 : F) two_ne_zero) := rfl
  rw [e0, Units.val_mul, ha _ (fun φ => by simp [map_ofNat]), n3, ← Finset.prod_mul_distrib, norm_prod] at k
  have e1 : ∀ φ : F →+* ℂ, ‖φ ((Units.mk0 (2 : F) two_ne_zero : Fˣ) : F) ^ a φ *
      ((‖φ ((Units.mk0 (2 : F) two_ne_zero : Fˣ) : F)‖ : ℝ) : ℂ) ^ (s : ℂ)‖ = (2 : ℝ) ^ ((a φ₀ : ℝ) + s) := fun φ => by
    rw [Units.val_mk0, map_ofNat, norm_mul, norm_zpow, hpar φ, Complex.norm_cpow_eq_rpow_re_of_pos (by simp),
      Real.rpow_add two_pos, Real.rpow_intCast]
    simp
  rw [Finset.prod_congr rfl fun φ _ => e1 φ, Finset.prod_const,
    pow_eq_one_iff_of_nonneg (by positivity) (Finset.card_pos.2 ⟨φ₀, Finset.mem_univ _⟩).ne'] at k
  have e2 : (a φ₀ : ℝ) + s = 0 := by
    have := congrArg Real.log k
    rw [Real.log_rpow two_pos, Real.log_one] at this
    exact (mul_eq_zero.1 this).resolve_right (Real.log_pos one_lt_two).ne'
  have hv : (normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hs, hv] at h1 h2
  have a1 : s < 1 := (Real.rpow_lt_rpow_left_iff (hq v)).1 (by rwa [Real.rpow_one])
  have a2 : 0 < 1 + s := (Real.rpow_lt_rpow_left_iff (hq v)).1 (by
    rwa [Real.rpow_zero, Real.rpow_add (zero_lt_one.trans (hq v)), Real.rpow_one])
  have b1 : (-1 : ℤ) < a φ₀ := by exact_mod_cast (show (-1 : ℝ) < a φ₀ by linarith)
  have b2 : a φ₀ < (1 : ℤ) := by exact_mod_cast (show (a φ₀ : ℝ) < 1 by linarith)
  funext φ
  rw [hpar φ, Pi.zero_apply]
  omega

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem inv_mem_eig {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

theorem ratio_roots {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (H : RatioW (wdOf h hl ι r)) {b c : ℂ}
    (hb : ((r ((frob h : Weil h) : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot b)
    (hc : ((r ((frob h : Weil h) : G F Ω)⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).IsRoot c) :
    ‖b‖ < (normV w : ℝ) * ‖c‖ := by
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp hr)
  have e := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  obtain ⟨b0, mb⟩ := inv_mem_eig (wdOf h hl ι r) (frob h) (b := b) (by rw [e]; exact hb)
  obtain ⟨c0, mc⟩ := inv_mem_eig (wdOf h hl ι r) (frob h) (b := c) (by rw [e]; exact hc)
  have k := H (frob h) (deg_frob) _ mc _ mb
  rw [norm_inv, norm_inv] at k
  have pb := norm_pos_iff.2 b0
  have pc := norm_pos_iff.2 c0
  rw [← div_eq_mul_inv, inv_eq_one_div, div_lt_div_iff₀ pc pb, one_mul] at k
  exact k

theorem ratioW_of_hasSat [IsTotallyReal F] (P : Hypotheses₂) {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    RatioW (wdOf h hl ι r) := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  exact H.ratio w hl A h rc hrc σ hσ
    (WD.unr_mono0 _ (unr_algNorm hrc σ B (((satLoc P F n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)))

theorem isWDOf_satR [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}
    (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := by
  rw [← (H.away w hl A h rc hrc σ hσ).eq_unr (unr_algNorm hrc σ S hS)]
  exact isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp H.cont)

end UpperTheory.GalN.V
end
end

