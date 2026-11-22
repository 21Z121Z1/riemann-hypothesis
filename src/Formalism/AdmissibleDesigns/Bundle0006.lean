import Formalism.AdmissibleDesigns.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.AdmissibleDesigns.LengthSemilinear
import Formalism.AdmissibleDesigns.FinDimOfLat
import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.AdmissibleDesigns.Bundle0005

-- bundled from Formalism.AdmissibleDesigns.HomeoKOf
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical Topology

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf

section HK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]

theorem homeoK_of (hF : IsOpenEmbedding (algebraMap O (FractionRing O))) : HomeoK (eK Bw) := by
  have hG := (T2.litGoodO l Bw.LL)
  have hOpen : IsOpen ((OL Bw.LL : Subalgebra ℤ_[l] (Br.LLw Bw)) : Set (Br.LLw Bw)) := by
    have h := hG.2.2.2.2
    rwa [show Set.range (algebraMap ↥(OL Bw.LL) ↥Bw.LL.1) = ((OL Bw.LL : Subalgebra ℤ_[l] (Br.LLw Bw)) : Set (Br.LLw Bw))
      from Subtype.range_coe] at h
  have hOL : IsOpenEmbedding (Subtype.val : ↥(OL Bw.LL) → Br.LLw Bw) := hOpen.isOpenEmbedding_subtypeVal
  constructor
  · refine continuous_of_continuousAt_zero (eK Bw) ?_
    have hc : Continuous fun x : O => eK Bw (algebraMap O (FractionRing O) x) := by
      have h1 : (fun x : O => eK Bw (algebraMap O (FractionRing O) x)) = fun x => ((Bw.eO x : ↥(OL Bw.LL)) : Br.LLw Bw) :=
        funext fun x => Br.toLLK_alg Bw x
      rw [h1]
      exact continuous_subtype_val.comp Bw.eO_cont
    show Filter.Tendsto (eK Bw) (𝓝 0) (𝓝 (eK Bw 0))
    rw [← map_zero (algebraMap O (FractionRing O)), ← hF.map_nhds_eq, Filter.tendsto_map'_iff]
    exact hc.tendsto 0
  · refine continuous_of_continuousAt_zero (eK Bw).symm ?_
    have hc : Continuous fun y : ↥(OL Bw.LL) => (eK Bw).symm (y : Br.LLw Bw) := by
      have h1 : (fun y : ↥(OL Bw.LL) => (eK Bw).symm (y : Br.LLw Bw)) =
          fun y => algebraMap O (FractionRing O) (Bw.eO.symm y) := by
        funext y
        apply (eK Bw).injective
        rw [RingEquiv.apply_symm_apply, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
        rfl
      rw [h1]
      exact hF.continuous.comp Bw.eO_symm_cont
    show Filter.Tendsto (eK Bw).symm (𝓝 0) (𝓝 ((eK Bw).symm 0))
    rw [show (0 : Br.LLw Bw) = ((0 : ↥(OL Bw.LL)) : Br.LLw Bw) from rfl, ← hOL.map_nhds_eq,
      Filter.tendsto_map'_iff]
    exact hc.tendsto 0

end HK

section Final

open NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]

theorem bKa_pi (n n' : Type) [Fintype n] [Fintype n']
    (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (n → FractionRing (D.nd.O i))
      (n' → FractionRing (D.nd.O i)))
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) {w : ℕ} (hw : w ∈ K.rowsN i dc)
    (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat (Dat w))
    (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (hF : IsOpenEmbedding (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    BKa i dc (fun _ => n → FractionRing (D.nd.O i)) (fun _ => n' → FractionRing (D.nd.O i)) Dat w :=
  bk_a_of_admitted_bk_a i dc _ _ Dat hBK hG hw hreal
    (rowIn_of i dc _ _ Dat hε (fun hn => ⟨homeoK_of (D.nbr i _ hn) hF,
      topMatch_pi (eK (D.nbr i _ hn)) n (homeoK_of (D.nbr i _ hn) hF),
      topMatch_pi (eK (D.nbr i _ hn)) n' (homeoK_of (D.nbr i _ hn) hF)⟩) hdr)

end Final

end Formalism.MainNotions.N.KBKa
end
end

-- bundled from Formalism.AdmissibleDesigns.LenComapSurj
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module

section Len

theorem len_comap_surj {O A B : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (f : A →ₗ[O] B) (hf : Function.Surjective f) (Q P : Submodule O B) :
    Module.length O (↥(Q.comap f) ⧸ (P.comap f).comap (Q.comap f).subtype) =
      Module.length O (↥Q ⧸ P.comap Q.subtype) := by
  let q : ↥(Q.comap f) →ₗ[O] ↥Q ⧸ P.comap Q.subtype :=
    (P.comap Q.subtype).mkQ ∘ₗ LinearMap.codRestrict Q (f ∘ₗ (Q.comap f).subtype) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hk : LinearMap.ker q = (P.comap f).comap (Q.comap f).subtype := by
    ext x
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)] [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
  (Ψ : M →ₛₗ[(e : R →+* S)] N) (hinj : Function.Injective Ψ)
  (Q P : Submodule R M) (Q' P' : Submodule S N)
  (hQ : ∀ y, y ∈ Q' ↔ ∃ x : M, x ∈ Q ∧ Ψ x = y) (hP : ∀ x ∈ Q, x ∈ P ↔ Ψ x ∈ P')

def resQ : ↥Q →ₛₗ[(e : R →+* S)] ↥Q' where
  toFun x := ⟨Ψ (x : M), (hQ _).2 ⟨x, x.2, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add Ψ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Ψ.map_smulₛₗ c (a : M))

include hinj in
theorem resQ_bij : Function.Bijective (resQ e Ψ Q Q' hQ) := by
  constructor
  · intro a b h
    have h' : Ψ (a : M) = Ψ (b : M) := congrArg Subtype.val h
    exact Subtype.ext (hinj h')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hQ y).1 hy
    exact ⟨⟨x, hx⟩, rfl⟩

include hinj hQ in

def resQE : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q' :=
  LinearEquiv.ofBijective (resQ e Ψ Q Q' hQ) (resQ_bij e Ψ hinj Q Q' hQ)

include hinj hQ in
theorem resQE_apply (x : ↥Q) : ((resQE e Ψ hinj Q Q' hQ x : ↥Q') : N) = Ψ (x : M) := rfl

include hinj hQ hP in

theorem len_semi :
    Module.length R (↥Q ⧸ P.comap Q.subtype) = Module.length S (↥Q' ⧸ P'.comap Q'.subtype) := by
  obtain ⟨E, hE⟩ : ∃ E : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q', ∀ x, ((E x : ↥Q') : N) = Ψ (x : M) :=
    ⟨resQE e Ψ hinj Q Q' hQ, resQE_apply e Ψ hinj Q Q' hQ⟩
  have hmap : (P.comap Q.subtype).map (E : ↥Q →ₛₗ[(e : R →+* S)] ↥Q') = P'.comap Q'.subtype := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hE]
      exact (hP x x.2).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hE] at hy
      exact ⟨x, (hP x x.2).2 hy, rfl⟩
  let F := Submodule.Quotient.equiv (P.comap Q.subtype) (P'.comap Q'.subtype) E hmap
  have h1 := Order.height_orderIso (Submodule.orderIsoMapComap F) ⊤
  rw [OrderIso.map_top] at h1
  rw [Module.length_eq_height, Module.length_eq_height]
  exact h1.symm

end Len

section Props

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))

def imRow (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  (Hf₁ i dc ρ₁ w).map (gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π (vD w) (hpD w) (heD w))

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def rowLenD (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (↥(Fs i dc VT VT' Dat w) ⧸
    (imRow i dc VT VT' Dat ρ₁ π vD hpD heD w).comap (Fs i dc VT VT' Dat w).subtype)

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  change _ = Br.toLLK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a)
  rw [Br.toLLK, IsFractionRing.lift_algebraMap]
  rfl

def RowSub (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsSubOfSums (repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x)))

def RowOrb : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) g x

def RowMat (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsMatLat (ρ := repL (eK (D.nbr i _ hn)) (Dat n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO (Dat n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ πx)))

def RowTop : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    (∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (c (Br.iota D.nbr i _ hn g))) → Continuous c) ∧
    (∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c)

def RowFin : Prop :=
  Module.Finite (D.nd.O i) T₁ ∧ Module.Free (D.nd.O i) T₁ ∧
  ∀ n ∈ K.rowsN i dc, Module.Finite (D.nd.O i) (Dat n).T' ∧ Module.Free (D.nd.O i) (Dat n).T' ∧
    ∀ v : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ t : (Dat n).T', (t : VT' n) = c • v

end Props

end Formalism.MainNotions.N.KRow

end
end

-- bundled from Formalism.AdmissibleDesigns.LocCont
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
      | exact continuous_id.matrix_map continuous_induced_dom
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont
      | exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont

theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl
    | simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]

end Formalism.MainNotions.N.KOrb

end
end

-- bundled from Formalism.AdmissibleDesigns.LocRepTriv
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

theorem unrFinIn (hA : EmbeddingTypes.UnramifiedTrivialH1f i dc) (l : K.Col i dc) : KFin.UnrFinIn i dc δO l := by
  intro f hf
  have hn := col_over i dc l
  refine Submodule.mem_map_of_mem ?_
  show (fun g => KHf.mkK (((KFin.uzOf i dc δO l f hf.1 : _ → _) g))) ∈
    ((KHf.fZ i dc (K.colIdx i dc l) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l)
      ↥(Ideal.span {δO})))).restrictScalars (D.nd.O i))
  rw [Submodule.restrictScalars_mem, KHf.fZ_pos i dc _ hn]
  have hU := hA (K.plOf i dc (K.colIdx i dc l)) hn (col_mem i dc l) (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn)
  let Bw := D.nbr i (K.plOf i dc (K.colIdx i dc l)) hn
  let V := KHf.MK (O := D.nd.O i) ↥(Ideal.span {δO})
  let c' : Br.G D.nbr i _ hn → Br.LLw Bw := fun g =>
    KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))
  have hc' : c' ∈ Z1ur (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) (Br.inert D.nbr i _ hn) := by
    refine ⟨⟨hf.2.2 hn, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · show c' (g * h) = c' g + c' h
      have h1 : f (Br.iota D.nbr i _ hn g * Br.iota D.nbr i _ hn h) =
          f (Br.iota D.nbr i _ hn g) + f (Br.iota D.nbr i _ hn h) := hf.1 _ _
      simp only [c', map_mul]
      rw [h1, map_add, map_add]
    · show c' g = 0 - 0
      rw [sub_zero]
      show KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g))) = 0
      rw [hf.2.1 _ hg, map_zero, map_zero]
  have hcf : c' ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) := by
    have hU' : finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) =
        Z1ur 1 (Br.inert D.nbr i _ hn) := hU
    rw [hU']
    exact hc'
  let v0 : KHf.TrV (KHf.eK Bw) V := KHf.mkK (⟨δO, Ideal.mem_span_singleton_self δO⟩ : ↥(Ideal.span {δO}))
  let f0 : Br.LLw Bw →ₗ[Br.LLw Bw] KHf.TrV (KHf.eK Bw) V := LinearMap.toSpanSingleton _ _ v0
  have hf0 : Continuous f0 := continuous_id.smul continuous_const
  let ρ' := KHf.repL (KHf.eK Bw) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l) ↥(Ideal.span {δO})))
    (Br.iota D.nbr i _ hn)
  have heq : ∀ g x, f0 ((1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) g x) = ρ' g (f0 x) :=
    fun g x => (locRep_triv (Br.iota D.nbr i _ hn g) (f0 x : V)).symm
  have key := (cocyclesFunctorial_holds _ _ _ _ _ _ (Br.PD D.loc D.nbr i _ hn) (Br.LLw Bw) (Br.LLw Bw) (KHf.TrV (KHf.eK Bw) V)
    1 ρ' f0 hf0 heq c').2 hcf
  let lhs : Br.G D.nbr i _ hn → KHf.TrV (KHf.eK Bw) V := fun g =>
    ((KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) : V) :
      KHf.TrV (KHf.eK Bw) V)
  show lhs ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) ρ'
  suffices hfun : lhs = ⇑f0 ∘ c' by
    rw [hfun]
    exact key
  funext g
  show _ = f0 (c' g)
  rw [LinearMap.toSpanSingleton_apply]
  show _ = ((KHf.eK Bw).symm (c' g) • (show V from v0) : V)
  simp only [c', RingEquiv.symm_apply_apply]
  rw [algebraMap_smul]
  rw [← map_smul]
  show KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) =
    KHf.mkK _
  congr 1
  apply Subtype.ext
  show δO * f (Br.iota D.nbr i _ hn g) = f (Br.iota D.nbr i _ hn g) * δO
  ring

theorem unrFin (hA : EmbeddingTypes.UnramifiedTrivialH1f i dc) : KHf.UnrFin i dc δO (KFin.uz i dc δO) :=
  KFin.unrFin i dc δO (unrHom i dc) (unrFinIn i dc δO hA)

end Rec

end Formalism.MainNotions.N.KUnr
end
end

-- bundled from Formalism.AdmissibleDesigns.MsContW
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msContW (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : K.TBa.MsContW (i := i) (r := r) hw :=
  fun x => locC_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) x

end Formalism.MainNotions.N.KOrb

end
end

