import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.FlagPlucker

theorem isAmpleLB_of_finite_fibres (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (hf : IsProper f)
    (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤)
    (hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Sp K ⟶ X),
      {a' : Sp K ⟶ X | a' ≫ f = a ≫ f ∧
        ∀ i, a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)}.Finite)
    (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i) (N : LB X) (hN : N.IsLB)
    (hcls : GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i)) : GlobalTheory.IsAmpleLB N := by
  obtain ⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩ :=
    GlobalTheory.AmpleSeparateOverRing.exists_ample_model R X f ι L hL M t ht w hw Finset.univ
  have : LocallyOfFiniteType (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ r
  have : IsProper (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ r
  have : LocallyQuasiFinite Ψ := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by
    by_cases hy : ∃ a : Spec (.of K) ⟶ X, a ≫ Ψ = y
    · obtain ⟨a, rfl⟩ := hy
      have hs : {a' : Spec (.of K) ⟶ X | a' ≫ Ψ = a ≫ Ψ}.Finite := (hfin K a).subset fun a' ha' => by
        obtain ⟨e1, e2⟩ := hinj K a' a ha'
        exact ⟨e1, fun i => e2 i (Finset.mem_univ i)⟩
      exact hs.to_subtype
    · haveI : IsEmpty {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x => hy ⟨x.1, x.2⟩⟩
      infer_instance
  have := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN := by
    rw [hc, hcls]
    exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _
  exact (isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN
    ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)

end GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

open Classical in

def ind (σ : E →+* ℂ) (m : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) ≤ m then 1 else 0

def plkU (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    Matrix (Fin Mc.n) (Fin (Dw.mult σ)) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  (chg Mc (F.M k).toMChart).map (π.appLE (Mc.U ⊓ (F.M k).U) (F.U k ⊓ π ⁻¹ᵁ Mc.U)
      (fun _ hp => ⟨hp.2, F.le k hp.1⟩)).hom *
    (F.u k σ).map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))

def plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) (m : Fin (Dw.mult σ))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) : Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  ((plkU F Mc k σ).submatrix r (Fin.castLE m.2)).det

abbrev plkNum (Mc : MChart Y) (m : ℕ) : ℕ := Fintype.card (Fin (m + 1) → Fin Mc.n)

def plkIdx (Mc : MChart Y) (m : ℕ) : Fin (plkNum Mc m + 1) → Option (Fin (m + 1) → Fin Mc.n) :=
  Fin.cases none fun i => some ((Fintype.equivFin _).symm i)

theorem plk_le (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (e : Ix Dw → ℤ) (j : ((F.LL e).pull g).ι) :
    ((F.LL e).pull g).U j ≤ g ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ π ⁻¹ᵁ Mc.U) :=
  fun _ hp => ⟨LB.wchart_le _ _ j PUnit.unit hp, hg trivial⟩

def plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) (j : ((F.LL (ind σ m)).pull g).ι) :
    Γ(T, ((F.LL (ind σ m)).pull g).U j) :=
  match plkIdx Mc m q with
  | none => 0
  | some r => (g.appLE _ _ (plk_le F Mc g hg (ind σ m) j)).hom (plkMinor F Mc (j PUnit.unit) σ m r)

end GlobalTheory.FlagPlucker

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {E E₁ E₂ : X.Modules} {N r s : ℕ}

theorem biprodMap_comp_biprodMap_π {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    biprod.map f g ≫ biprod.map (cokernel.π f) (cokernel.π g) = 0 := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

def cokernelCoforkBiprodMap {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    CokernelCofork (biprod.map f g) :=
  CokernelCofork.ofπ (biprod.map (cokernel.π f) (cokernel.π g)) (biprodMap_comp_biprodMap_π f g)

def isColimitCokernelCoforkBiprodMap {A B C D : X.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    IsColimit (cokernelCoforkBiprodMap f g) :=
  CokernelCofork.IsColimit.ofπ _ (biprodMap_comp_biprodMap_π f g)
    (fun k hk => biprod.desc
      (cokernel.desc f (biprod.inl ≫ k) (by
        have := congrArg (biprod.inl ≫ ·) hk
        simpa using this))
      (cokernel.desc g (biprod.inr ≫ k) (by
        have := congrArg (biprod.inr ≫ ·) hk
        simpa using this)))
    (fun k hk => by
      refine biprod.hom_ext' _ _ ?_ ?_ <;> simp)
    (fun k hk m hm => by
      apply biprod.hom_ext'
      · refine (cancel_epi (cokernel.π f)).1 ?_
        have := congrArg (biprod.inl ≫ ·) hm
        simpa [cokernelCoforkBiprodMap] using this
      · refine (cancel_epi (cokernel.π g)).1 ?_
        have := congrArg (biprod.inr ≫ ·) hm
        simpa [cokernelCoforkBiprodMap] using this)

theorem isSubbundle_biprodMap {A B C D : X.Modules} {f : A ⟶ B} {g : C ⟶ D}
    (hf : VB.IsSubbundle f) (hg : VB.IsSubbundle g) : VB.IsSubbundle (biprod.map f g) := by
  obtain ⟨_, m, hm⟩ := hf
  obtain ⟨_, n, hn⟩ := hg
  exact ⟨inferInstance, m + n, (hm.biprod hn).of_iso
    ((isColimitCokernelCoforkBiprodMap f g).coconePointUniqueUpToIso (colimit.isColimit _))⟩

variable (fl : Flag E N)

@[reassoc (attr := simp)]
theorem eqToHom_ι {a b : Fin (N + 1)} (e : a = b) : eqToHom (congrArg fl.F e) ≫ fl.ι b = fl.ι a := by
  subst e; simp

def incl (a b : Fin (N + 1)) (h : (b : ℕ) = a ∨ (b : ℕ) = a + 1) : fl.F a ⟶ fl.F b :=
  if h' : (b : ℕ) = a then eqToHom (congrArg fl.F (Fin.ext h'.symm)) else
    eqToHom (congrArg fl.F (Fin.ext rfl : a = (⟨a, by omega⟩ : Fin N).castSucc)) ≫
      fl.step ⟨a, by omega⟩ ≫
      eqToHom (congrArg fl.F (Fin.ext (by simp; omega) : (⟨a, by omega⟩ : Fin N).succ = b))

@[reassoc (attr := simp)]
theorem incl_ι (a b : Fin (N + 1)) (h : (b : ℕ) = a ∨ (b : ℕ) = a + 1) :
    fl.incl a b h ≫ fl.ι b = fl.ι a := by
  unfold incl
  split_ifs with h'
  · exact fl.eqToHom_ι (Fin.ext h'.symm)
  · rw [Category.assoc, Category.assoc, fl.eqToHom_ι, fl.step_ι, fl.eqToHom_ι]
    all_goals ext; simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

theorem isIso_ι_of_eq {a : Fin (N + 1)} (e : a = Fin.last N) : IsIso (fl.ι a) := by
  subst e; infer_instance

def fstIdx (r s : ℕ) (i : Fin (r + s + 1)) : Fin (r + 1) := ⟨min (i : ℕ) r, by omega⟩

def sndIdx (r s : ℕ) (i : Fin (r + s + 1)) : Fin (s + 1) := ⟨(i : ℕ) - r, by omega⟩

theorem fstIdx_step (i : Fin (r + s)) : (fstIdx r s i.succ : ℕ) = fstIdx r s i.castSucc ∨
    (fstIdx r s i.succ : ℕ) = fstIdx r s i.castSucc + 1 := by
  simp only [fstIdx, Fin.val_succ, Fin.val_castSucc]; omega

theorem sndIdx_step (i : Fin (r + s)) : (sndIdx r s i.succ : ℕ) = sndIdx r s i.castSucc ∨
    (sndIdx r s i.succ : ℕ) = sndIdx r s i.castSucc + 1 := by
  simp only [sndIdx, Fin.val_succ, Fin.val_castSucc]; omega

def biprod (fl₁ : Flag E₁ r) (fl₂ : Flag E₂ s) : Flag (E₁ ⊞ E₂) (r + s) where
  F i := fl₁.F (fstIdx r s i) ⊞ fl₂.F (sndIdx r s i)
  ι i := biprod.map (fl₁.ι _) (fl₂.ι _)
  isSubbundle i := isSubbundle_biprodMap (fl₁.isSubbundle _) (fl₂.isSubbundle _)
  isVB i := by
    have h := (fl₁.isVB (fstIdx r s i)).biprod (fl₂.isVB (sndIdx r s i))
    have e : ((fstIdx r s i : ℕ) + (sndIdx r s i : ℕ)) = i := by
      simp only [fstIdx, sndIdx]; omega
    rwa [e] at h
  step i := biprod.map (fl₁.incl _ _ (fstIdx_step i)) (fl₂.incl _ _ (sndIdx_step i))
  step_ι i := by refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  isIso_last := by
    have := fl₁.isIso_ι_of_eq (a := fstIdx r s (Fin.last (r + s)))
      (Fin.ext (by simp [fstIdx]))
    have := fl₂.isIso_ι_of_eq (a := sndIdx r s (Fin.last (r + s)))
      (Fin.ext (by simp [sndIdx]))
    exact inferInstanceAs (IsIso (biprod.mapIso (asIso (fl₁.ι _)) (asIso (fl₂.ι _))).hom)

theorem biprod_ι (fl₁ : Flag E₁ r) (fl₂ : Flag E₂ s) (i : Fin (r + s + 1)) :
    (fl₁.biprod fl₂).ι i = biprod.map (fl₁.ι (fstIdx r s i)) (fl₂.ι (sndIdx r s i)) := rfl

end GlobalTheory.Vert.Flag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainSaturatedFundamentalSetFrames
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FundFrames

open scoped Pointwise

theorem isFundamentalDomain_satFrames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  intro E _ _ _ r X c hH x0 ho FF hF Λ hΛ
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  set S := GlobalTheory.Unfold.satFrames X x0 FF with hSdef
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1

  have hmemT : ∀ (s : Λ) (g : RealGrp X) (γ : GL (Fin r) E), lact γ (baseFr X) = frameOf X s →
      (g ∈ s • (frameOf X ⁻¹' S) ↔ lact γ⁻¹ (frameOf X g) ∈ S) := by
    intro s g γ e
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    have h1 : lact γ (frameOf X (s⁻¹ • g)) = frameOf X g := by
      rw [GlobalTheory.PeterssonCompare.lact_frameOf X e, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv,
        mul_inv_cancel_left]
    have h2 : frameOf X (s⁻¹ • g) = lact γ⁻¹ (frameOf X g) := by
      rw [← h1, FundSetPf.lact_inv]
    rw [h2]
  refine ⟨(GlobalTheory.PeterssonCompare.measurable_frameOf X hS).nullMeasurableSet, ?_, ?_⟩
  ·
    set G' : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun y => lact (γ.1)⁻¹ y) ⁻¹' S with hG'def
    have hG' : MeasurableSet G' :=
      MeasurableSet.iUnion fun γ => (GlobalTheory.Unfold.continuous_lact X _).measurable hS
    have hmemG : ∀ y, y ∈ G' ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ S := by
      intro y
      simp only [G', Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨γ, hy⟩; exact ⟨γ.1, γ.2, hy⟩
      · rintro ⟨γ, hγ, hy⟩; exact ⟨⟨γ, hγ⟩, hy⟩
    have hGB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ G' ↔ y ∈ G' := by
      intro y b hb
      simp only [hmemG, FundSetPf.lact_rmul, hSdef, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF _ hb]
    set φ : Frame X.Ψ r → ℝ≥0∞ := G'ᶜ.indicator 1 with hφdef
    have hφm : Measurable φ := measurable_const.indicator hG'.compl
    have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
      intro x _ b hb
      have hiff : rmul x b ∈ G'ᶜ ↔ x ∈ G'ᶜ := by
        simp only [Set.mem_compl_iff, hGB x b hb]
      by_cases hx : x ∈ G'ᶜ
      · rw [hφdef, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]; rfl
      · rw [hφdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hiff.1 h'))]
    have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
    have h1 : GlobalTheory.SubgroupUnfold.IsIsom X.Gm (1 : GL (Fin r) E) := by
      intro v w; simp
    have hae := GlobalTheory.SubgroupUnfold.ae_mem_orbit_satFrames X ho hF hbo h1
    have hz : ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) = 0 := by
      rw [← lintegral_zero (μ := muF X (baseFr X))]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with z hz
      obtain ⟨γ, hγ, hm⟩ := hz
      rw [mul_one] at hm
      have : cpt X (baseFr X) z ∉ G'ᶜ := by
        rw [Set.mem_compl_iff, not_not, hmemG]; exact ⟨γ, hγ, hm⟩
      show φ _ = 0
      rw [hφdef, Set.indicator_of_notMem this]
    have hint := hH φ hφm hφB
    rw [hz, mul_zero] at hint
    have hae2 := (lintegral_eq_zero_iff (hφm.comp (GlobalTheory.PeterssonCompare.measurable_frameOf X))).1 hint
    filter_upwards [hae2] with g hg
    have hg' : φ (frameOf X g) = 0 := hg
    have hn : frameOf X g ∉ G'ᶜ := fun hm => by
      rw [hφdef, Set.indicator_of_mem hm] at hg'; exact one_ne_zero hg'
    rw [Set.mem_compl_iff, not_not, hmemG] at hn
    obtain ⟨γ, hγ, hm⟩ := hn
    obtain ⟨s, hs⟩ := GlobalTheory.PeterssonCompare.exists_translation X (X.Γ.inv_mem hγ)
    refine ⟨⟨s, (hΛ s).2 ⟨γ⁻¹, X.Γ.inv_mem hγ, hs⟩⟩, ?_⟩
    show frameOf X (s * g) ∈ S
    rw [← GlobalTheory.PeterssonCompare.lact_frameOf X hs]
    exact hm
  ·
    intro s t hst
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun g hgs hgt => hst ?_)
    obtain ⟨γ, hγ, e⟩ := (hΛ s).1 s.2
    obtain ⟨γ', hγ', e'⟩ := (hΛ t).1 t.2
    have h1 := (hmemT s g γ e).1 hgs
    have h2 := (hmemT t g γ' e').1 hgt
    obtain rfl := GlobalTheory.Unfold.unique_translate X hF hγ hγ' h1 h2
    exact Subtype.ext (GlobalTheory.PeterssonCompare.frameOf_injective X (e.symm.trans e'))

end GlobalTheory.FundFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisCartDesc

theorem epi_of_isGaloisCover {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) : Epi π := by
  refine ⟨fun {Z} g₁ g₂ e ↦ ?_⟩
  obtain ⟨f', -, hu⟩ := h.existsUnique_desc (π ≫ g₁) (fun a ↦ by rw [← Category.assoc, h.inv])
  exact (hu g₁ rfl).trans (hu g₂ e.symm).symm

theorem epi_pullback_fst {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {T : Scheme.{0}} (t : T ⟶ Y) : Epi (pullback.fst t π) := by
  let ρ' : Ga → (pullback t π ⟶ pullback t π) := fun a ↦
    pullback.map t π t π (𝟙 _) (ρ a) (𝟙 _) (by simp) (by simp [h.inv])
  have hg : GlobalTheory.ZM.IsGaloisCover Ga ρ' (pullback.fst t π) :=
    h.of_isPullback (IsPullback.of_hasPullback t π).flip
      (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_snd])
      (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_fst, Category.comp_id])
  exact epi_of_isGaloisCover hg

theorem isGrpPullback_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y)
    (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left)
    (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ →
    IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ φ₁ ψ φ hG hφ₁ hψ hφ

  let τ : Ga → (A'.left ⟶ A'.left) := fun a ↦
    hφ₁.1.lift φ₁ (A'.hom ≫ ρ₁ a) (by rw [hφ₁.1.w, Category.assoc, hG.inv])
  have hτ₁ : ∀ a, τ a ≫ φ₁ = φ₁ := fun a ↦ hφ₁.1.lift_fst _ _ _
  have hτ₂ : ∀ a, τ a ≫ A'.hom = A'.hom ≫ ρ₁ a := fun a ↦ hφ₁.1.lift_snd _ _ _
  have gφ₁ : GlobalTheory.ZM.IsGaloisCover Ga τ φ₁ := hG.of_isPullback hφ₁.1.flip hτ₂ hτ₁
  have eφ₁ : Epi φ₁ := epi_of_isGaloisCover gφ₁

  have w : φ ≫ B.hom = A.hom ≫ f := by
    rw [← cancel_epi φ₁, reassoc_of% hφ, hψ.1.w, ← reassoc_of% hφ₁.1.w]

  let q : A'.left ⟶ pullback B.hom f := pullback.lift ψ (A'.hom ≫ π₁) (by rw [hψ.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd B.hom f = A'.hom ≫ π₁ := pullback.lift_snd _ _ _
  have hsq : IsPullback q A'.hom (pullback.snd B.hom f) π₁ := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback B.hom f)
    rw [hq₁]
    exact hψ.1
  have hτq : ∀ a, τ a ≫ q = q := fun a ↦ by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, ← hφ, reassoc_of% hτ₁ a]
    · rw [Category.assoc, hq₂, reassoc_of% hτ₂ a, hG.inv]
  have gq : GlobalTheory.ZM.IsGaloisCover Ga τ q := hG.of_isPullback hsq.flip hτ₂ hτq
  have eq : Epi q := epi_of_isGaloisCover gq
  obtain ⟨d, hd, -⟩ := gq.existsUnique_desc φ₁ hτ₁
  let c : A.left ⟶ pullback B.hom f := pullback.lift φ A.hom w
  have hc : φ₁ ≫ c = q := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, hq₁]
      rw [pullback.lift_fst, hφ]
    · simp only [c, Category.assoc, hq₂]
      rw [pullback.lift_snd, hφ₁.1.w]
  have hcd : c ≫ d = 𝟙 _ := by rw [← cancel_epi φ₁, reassoc_of% hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 _ := by rw [← cancel_epi q, reassoc_of% hd, hc, Category.comp_id]
  let i : A.left ≅ pullback B.hom f := ⟨c, d, hcd, hdc⟩
  refine ⟨IsPullback.of_iso_pullback ⟨w⟩ i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ?_⟩

  intro T x y x₀ y₀ hx hy
  let e : pullback T.hom π₁ ⟶ T.left := pullback.fst T.hom π₁
  have ee : Epi e := epi_pullback_fst hG T.hom
  let T₁ : Over S₁ := Over.mk (pullback.snd T.hom π₁)
  let j : Over.mk (T₁.hom ≫ π₁) ⟶ T := Over.homMk e (by simp [T₁, e, pullback.condition])
  let j' : Over.mk (T₁.hom ≫ π₁ ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
    Over.homMk e (by simp [T₁, e, pullback.condition_assoc])
  have lift : ∀ z : T ⟶ A, ∃ z₁ : T₁ ⟶ A', z₁.left ≫ φ₁ = e ≫ z.left := fun z ↦
    ⟨Over.homMk (hφ₁.1.lift (e ≫ z.left) (pullback.snd T.hom π₁)
      (by simp [e, pullback.condition])) (hφ₁.1.lift_snd _ _ _), hφ₁.1.lift_fst _ _ _⟩
  obtain ⟨x₁, hx₁⟩ := lift x
  obtain ⟨y₁, hy₁⟩ := lift y
  have a₁ : ((j ≫ x) * (j ≫ y)).left = (x₁ * y₁).left ≫ φ₁ :=
    hφ₁.2 T₁ x₁ y₁ (j ≫ x) (j ≫ y) (by simp [j, hx₁]) (by simp [j, hy₁])
  have a₂ : ((j' ≫ x₀) * (j' ≫ y₀)).left = (x₁ * y₁).left ≫ ψ :=
    hψ.2 T₁ x₁ y₁ (j' ≫ x₀) (j' ≫ y₀) (by simp [j', hx, ← hφ, reassoc_of% hx₁])
      (by simp [j', hy, ← hφ, reassoc_of% hy₁])
  rw [← MonObj.comp_mul] at a₁ a₂
  rw [← cancel_epi e]
  have b₁ : e ≫ (x * y).left = (x₁ * y₁).left ≫ φ₁ := by simpa [j] using a₁
  have b₂ : e ≫ (x₀ * y₀).left = (x₁ * y₁).left ≫ ψ := by simpa [j'] using a₂
  rw [b₂, reassoc_of% b₁, hφ]

end GlobalTheory.GaloisCartDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteV
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PureTransc

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let K := FractionRing P
  letI : Algebra (P ⊗[k] A) (K ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (K ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

theorem isIntegral_of_isPullback : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X),
    IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) →
    IsIntegral X' := by
  intro k _ N X X' _ f f' π H

  have chart (x : X) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : IsDomain A)
      (j : Sp A ⟶ X) (_ : IsOpenImmersion j) (q : PrimeSpectrum A),
      j q = x ∧ j ≫ f = spMap (algebraMap k A) := by
    obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f x
    have : Nonempty (Spec (.of A)) := ⟨q⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion j
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    exact ⟨A, _, _, this, j, inferInstance, q, hq, hj⟩
  have lift {A : Type} [CommRing A] [Algebra k A] [IsDomain A] (j : Sp A ⟶ X) [IsOpenImmersion j]
      (hj : j ≫ f = spMap (algebraMap k A)) (x' : X') (hx : π x' ∈ Set.range j) :
      ∃ (j₀ : Sp (FractionRing (MvPolynomial (Fin N) k) ⊗[k] A) ⟶ X') (_ : IsOpenImmersion j₀),
        x' ∈ Set.range j₀ := by
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    refine ⟨j₀, hj₀, ?_⟩
    have hr : x' ∈ Set.range (Limits.pullback.fst π j) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨z, rfl⟩ := hr
    exact ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst]⟩
  have hflat : Flat π := by
    refine MorphismProperty.of_isPullback H.flip ?_
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact GlobalTheory.GeomIrr.flat_of_field _
  have : IsReduced X' := by
    have (x' : X') : _root_.IsReduced (X'.presheaf.stalk x') := by
      obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (π x')
      obtain ⟨j₀, _, z, rfl⟩ := lift j hj x' ⟨q, hq⟩
      have := isDomain_tensor k (Fin N) A
      exact isReduced_of_injective
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (genericPoint X)
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    have := isDomain_tensor k (Fin N) A
    have hirr : IsIrreducible (Set.range j₀) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ j₀.continuous.continuousOn
    have hdense : closure (Set.range j₀) = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => ?_
      obtain ⟨y, hy, e⟩ := Flat.generalizingMap π (genericPoint_specializes (π x'))
      have hr : y ∈ Set.range (Limits.pullback.fst π j) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hr
      have hy' : y ∈ Set.range j₀ :=
        ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst, hz]⟩
      exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy)
    refine (irreducibleSpace_def X').2 ?_
    rw [Set.top_eq_univ, ← hdense]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X'

end GlobalTheory.PureTransc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSetStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  first | exact @GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | exact GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | (intros; apply GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeightStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  first | exact @GlobalTheory.LamSize.lamSup_le | exact GlobalTheory.LamSize.lamSup_le | (intros; apply GlobalTheory.LamSize.lamSup_le <;> assumption)
end

