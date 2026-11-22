import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0043

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CellRelIff
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def Ak : Subgroup K := S.subgroupOf K

def πk (hD : Data W S N' K π) : K →* Ak S K where
  toFun k := ⟨⟨π k, hD.kπ k k.2⟩, by show π k ∈ S; exact hD.mem k⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

theorem cellRel_iff (hD : Data W S N' K π) (k₁ k₂ : K) :
    (cellRel W N' K g).r (toCell W S N' K π g hD k₁) (toCell W S N' K π g hD k₂) ↔
      ∃ n ∈ (πk W S N' K π hD).ker, ∃ h ∈ Hk W K g, k₂ = n * k₁ * h := by
  show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _
  constructor
  · rintro ⟨hK, hN⟩
    set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx
    refine ⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      have h1 : π x = 1 := (hD.ker x).1 hN
      ext
      simp [πk, h1]
    · rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]
      refine ⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have e2 := cell_smul W S N' K π hD ((k₂ : G) * g)
      have e1 := cell_smul W S N' K π hD ((k₁ : G) * g)
      calc ((k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂ : K) : G) • g • W
          = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • ((cell π ((k₂ : G) * g))⁻¹ • (((k₂ : G) * g) • W)) := by
            rw [← mul_smul, ← mul_smul, ← mul_smul]
            congr 1
            push_cast
            rw [hx]
            group
        _ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]
        _ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp
    · ext
      push_cast
      group
  · rintro ⟨n, hn, h, hh, rfl⟩
    have hπn : π (n : G) = 1 := by
      rw [MonoidHom.mem_ker] at hn
      have := congrArg (fun a : Ak S K => ((a : K) : G)) hn
      simpa [πk] using this
    have hh' : (h : G) • g • W = g • W := by
      rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf] at hh
      exact hh.2
    have hs : g⁻¹ * (h : G) * g ∈ S := by
      rw [← hD.stab]
      rw [mul_smul, mul_smul, hh', ← mul_smul]
      simp
    have key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g) := by
      have e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g) := by
        push_cast
        group
      simp only [cell]
      rw [e, map_mul, map_mul, hπn, hD.id _ hs]
      group
    rw [key, mul_inv_cancel_right]
    exact ⟨n.2, (hD.ker n).2 hπn⟩

end Formalism.L2.SG.Pf.CountAb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure
section
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finiteLevelVolume_of_measure (hM : X.MeasTie hb) : FiniteLevelVolumeEquality X hb := by
  unfold FiniteLevelVolumeEquality
  rw [hM.2.2.1]
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  let e := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).toHomeomorph.toMeasurableEquiv
  have he : (X.toFin hb : X.B.I.Gf → _) = e := rfl
  have hK : levelUnitary X hb = e '' X.K2 := rfl
  rw [hK, he, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]

theorem mem_rr_iff (x : X.B.I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ↔
      toHA X.B.I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I (toHA X.B.I hb) (toHA_isBridge X.B.I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      h ∈ ratHA X.B.I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA X.B.I hb).injective hyx]

theorem covolTie_of (hM : X.MeasTie hb) : CovolTie X := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' X.B.I X.B.μf
  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨X.B.fund_spec.1, X.B.fund_spec.2.1, X.B.fund_spec.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
  let e := (toHA X.B.I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
    { toFun := fun g => ⟨(toHA X.B.I hb).symm (g : HA _ _ _), (mem_rr_iff X hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA X.B.I hb x, (mem_rr_iff X hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  haveI : Countable Γ := Function.Injective.countable eΓ.injective
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((X.B.I.muA X.B.μf).map e) (X.B.I.muA X.B.μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' X.B.fund) X.measG.μG := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : X.B.I.GA) * x) = (g : HA _ _ _) * e x
    show toHA X.B.I hb ((toHA X.B.I hb).symm g * x) = (g : HA _ _ _) * toHA X.B.I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmap : X.measG.μG (e '' X.B.fund) = X.B.I.muA X.B.μf X.B.fund := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]
  haveI : (X.measG.μG).IsHaarMeasure := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    exact (toHA X.B.I hb).isHaarMeasure_map (X.B.I.muA X.B.μf)
  haveI : (X.measG.μG).IsMulLeftInvariant := inferInstance
  haveI : MeasurableConstSMul Γ (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    ⟨fun c => (continuous_mul_left (c : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurable⟩
  unfold CovolTie covolBy
  split_ifs with h
  · have h1 : IsFundamentalDomain Γ h.choose X.measG.μG := h.choose_spec
    rw [h1.measure_eq hfd, hmap]
    rfl
  · exact absurd ⟨_, hfd⟩ h

section MassData

open Formalism.L2.SG.MassDataConc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX_holds (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X :=
  MassDataDstarX X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq L A hH hKpp (finiteLevelVolume_of_measure X hb hH.1)
    (covolTie_of X hb hH.1)

end MassData

end Formalism.L2.SG.IntegralApproximation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianW0SpanZero
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Psi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem MMfam_mem_sup (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
  have hf : ∀ a, t.f a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hf' : ∀ a, t.f' a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  unfold HermSp.MMfam
  rcases M.split with _ | g
  · rcases i with a | a
    · exact hf a
    · exact hf' a
  · rcases i with a | a
    · exact hf a
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' a) (hf a))

theorem hermitian_W0_span_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h w m = 0 := by
  have hle : Submodule.span E (Set.range (H.MMfam t)) ≤ H.Xp t.f ⊔ H.Xp t.f' :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)
  exact hw m (hle hm)

theorem hermitian_span_W0_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h m w = 0 := by
  rw [H.h_herm, hermitian_W0_span_zero H t hw hm, map_zero]

def psiSharp (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    ↥(ThSharp H t₁ N₁) ≃ₗ[M.L.O] ↥(ThSharp H t₂ N₂) where
  toFun x := ⟨ψ ⟨x.1, x.2.1⟩, (ψ ⟨x.1, x.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₂.f t₂.f' := hN₂ hn
    have e : ψ (ψ.symm ⟨n, hnW⟩) = ⟨n, hnW⟩ := ψ.apply_symm_apply _
    have h1 : ((ψ.symm ⟨n, hnW⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁ := by
      rw [hN, e]; exact hn
    have h2 := x.2.2 _ h1
    have h3 := hψ ⟨x.1, x.2.1⟩ (ψ.symm ⟨n, hnW⟩)
    rw [e] at h3
    rw [h3]
    exact h2⟩
  invFun y := ⟨ψ.symm ⟨y.1, y.2.1⟩, (ψ.symm ⟨y.1, y.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₁.f t₁.f' := hN₁ hn
    have h1 : ((ψ ⟨n, hnW⟩ : ↥(H.W0 t₂.f t₂.f')) : V) ∈ N₂ := (hN ⟨n, hnW⟩).1 hn
    have h2 := y.2.2 _ h1
    have h3 := hψ (ψ.symm ⟨y.1, y.2.1⟩) ⟨n, hnW⟩
    rw [ψ.apply_symm_apply] at h3
    rw [← h3]
    exact h2⟩
  map_add' x y := by
    apply Subtype.ext
    have e : (⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        ⟨x.1, x.2.1⟩ + ⟨y.1, y.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) + ((ψ ⟨y.1, y.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    have e : (⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        (c : E) • ⟨x.1, x.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      (c : E) • ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_smul]
    rfl
  left_inv x := by
    apply Subtype.ext
    show ((ψ.symm ⟨(ψ ⟨x.1, x.2.1⟩ : V), _⟩ : ↥(H.W0 t₁.f t₁.f')) : V) = x.1
    rw [Subtype.coe_eta, ψ.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    show ((ψ ⟨(ψ.symm ⟨y.1, y.2.1⟩ : V), _⟩ : ↥(H.W0 t₂.f t₂.f')) : V) = y.1
    rw [Subtype.coe_eta, ψ.apply_symm_apply]

theorem psiSharp_val (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) (x : ↥(ThSharp H t₁ N₁)) :
    ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) = (ψ ⟨x.1, x.2.1⟩ : V) := rfl

def psiTilde (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    DDW H t₁ N₁ ≃ₗ[M.L.O] DDW H t₂ N₂ :=
  Submodule.Quotient.equiv _ _ (psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) ∈ N₂
      rw [psiSharp_val]
      exact (hN _).1 hx
    · intro hy
      refine ⟨(psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      change ((ψ.symm ⟨y.1, y.2.1⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁
      rw [hN (ψ.symm ⟨y.1, y.2.1⟩), ψ.apply_symm_apply]
      exact hy)

theorem psiTilde_mk (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) (x : ↥(ThSharp H t₁ N₁)) :
    psiTilde H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN (dwMk H t₁ N₁ x) =
      dwMk H t₂ N₂ (psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x) := rfl

end Psi

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {α : Type*} {r : α → α → Prop}

theorem eqvGen_iff_of (f : α → Prop) (hf : ∀ a b, r a b → (f a ↔ f b)) {a b : α} (h : Relation.EqvGen r a b) :
    (f a ↔ f b) := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqvGen_eq_of {β : Type*} (f : α → β) (hf : ∀ a b, r a b → f a = f b) {a b : α} (h : Relation.EqvGen r a b) :
    f a = f b := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Gen

theorem relRepC : RelRepC := by
  intro D X Y u u' t hr hG
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨hGF, -, hRF, -, -⟩ := term_function_const D u u' (X.Fu u) t.lam hΛ

  set x : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') := ⟨frq X t.rep, t.rep.2.2.2.2⟩ with hx
  have hcls : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := rfl
  constructor
  · obtain ⟨F', ⟨hP, hmk⟩, hrel⟩ := hr
    have hcls' : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := hcls
    rw [hcls'] at hmk
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')) ⟨F', hP⟩ x :=
      Quot.eqvGen_exact hmk
    exact (eqvGen_iff_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Relevant D.host.F (lf D (X.Fu u)).fl y.1.fl) (fun a b hab => hRF a b hab) he).1 hrel
  · have hG' : TermDef.Gt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')
        (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x) = 0 := hG
    unfold TermDef.Gt at hG'
    have hout := Quot.out_eq (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u'))
        (Quot.out (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)) x :=
      Quot.eqvGen_exact hout
    have := eqvGen_eq_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Gval (lf D (X.Fu u)) y.1) (fun a b hab => hGF a b hab) he
    rw [← this]; exact hG'

theorem kppOffC_of_steps (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC) (hV : LemmaVC)
    (hCov : CovRepC) (hSch : SchurNFC) : Formalism.L2.SG.RowsConc.KppOffC :=
  kppOffC_of_cut hFold hFE hOI hV relRepC hCov hSch

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SchurCoreA : Prop :=
  ∀ (k : ℕ) (ι : Type) [Fintype ι] (V V' : ι → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    [∀ i, NormedAddCommGroup (V' i)] [∀ i, InnerProductSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
    (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
    (tens : (∀ i, V i) → W) (tens' : (∀ i, V' i) → W'),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    (∀ x y, ⟪tens' x, tens' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Submodule.span ℂ (Set.range tens') = ⊤ →
    ∀ (π : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V i →L[ℂ] V i)) (π' : ∀ i, Matrix (Fin k) (Fin k) ℂ → (V' i →L[ℂ] V' i))
      (lam lam' : ι → Fin k → ℝ),
    (∀ i, IsHCTypeU k (lam i) (π i)) → (∀ i, IsHCTypeU k (lam' i) (π' i)) →
    ∀ i₀ : ι, lam i₀ ≠ lam' i₀ →
    ∀ (C : ι → Matrix (Fin k) (Fin k) ℂ), (∀ i, C i ∈ UJset (allPos k)) →
    ∀ P : W' →L[ℂ] W,
      (∀ M : ι → Matrix (Fin k) (Fin k) ℂ, (∀ i, M i ∈ UJset (allPos k)) →
        ∃ (A : W →L[ℂ] W) (B : W' →L[ℂ] W'),
          (∀ x, A (tens x) = tens (fun i => π i (M i) (x i))) ∧
          (∀ x, B (tens' x) = tens' (fun i => π' i (C i * M i * (C i)ᴴ) (x i))) ∧
          A.comp P = P.comp B) →
      P = 0

def LeviTens : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ h ∈ X.SinfU u, ∀ x : ∀ v, X.Vloc u v,
    X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (matW X.B.I (X.wfr u v) v h) (x v))

def WfrSpan : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ),
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0 ∧ hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) y = 0) →
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) y = 0 →
    y = ∑ b, hJ (X.B.I.ε v) (X.wfr u v b) y • X.wfr u v b

def CplxKer : Prop :=
  ∀ (E : Type) [Field E] (φ : E →+* ℂ) (m N : ℕ) (A : Matrix (Fin m) (Fin N) E) (c : Fin N → ℂ),
    A.map φ *ᵥ c = 0 → c ∈ Submodule.span ℂ ((fun s : Fin N → E => fun i => φ (s i)) '' {s | A *ᵥ s = 0})

variable {D : D7} in

def spanAt (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (U : Submodule D.host.E (VS D).V) :
    Submodule ℂ (Fin X.B.I.n → ℂ) :=
  Submodule.span ℂ ((fun p => rv X.B.I v (X.crd p)) '' (U : Set (VS D).V))

def CplxNF : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ v : InfinitePlace X.B.I.F,
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (lf D (X.Fu u)).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (lf D (X.Fu u)).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y : Fin X.B.I.n → ℂ, (∀ p ∈ (frq X q).fl.Xplus, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        ∃ x ∈ spanAt X v (frq X q).fl.X,
          ∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (y - x) = 0) ∧
      (∀ y ∈ spanAt X v (lf D (X.Fu u)).fl.X, (∀ p ∈ fixedSubspaceOfRepresentative X q, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) y = 0) →
        y ∈ spanAt X v (Isp (lf D (X.Fu u)).fl (frq X q).fl))

def GeomB : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∃ C : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, C v ∈ UJset (allPos D.R.k)) ∧
      ∀ M : InfinitePlace X.B.I.F → Matrix (Fin D.R.k) (Fin D.R.k) ℂ, (∀ v, M v ∈ UJset (allPos D.R.k)) →
        ∃ h ∈ pointwiseStabilizerInfinite X q,
          (∀ x, X.piU u h (X.tensU u x) = X.tensU u (fun v => X.piLoc u v (M v) (x v))) ∧
          (∀ x, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1) (X.tensU u' x) =
            X.tensU u' (fun v => X.piLoc u' v (C v * M v * (C v)ᴴ) (x v)))

end PI.SchurPlaces
end
end

