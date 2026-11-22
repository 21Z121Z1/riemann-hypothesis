import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.WdRestrict
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.CMCompositionLift
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CMCompositionLift

abbrev cmComp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω) : CMExt E Ω :=
  letI : Algebra E Y.M := ((algebraMap X.M Y.M).comp (algebraMap E X.M)).toAlgebra
  { M := Y.M
    tower := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply E X.M Ω x, IsScalarTower.algebraMap_apply X.M Y.M Ω]
      rfl }

theorem resG_comp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω)
    (g : G (cmComp X Y).M Ω) :
    resG E (E' := (cmComp X Y).M) (Ω := Ω) g = resG E (E' := X.M) (Ω := Ω) (resG X.M (E' := Y.M) (Ω := Ω) g) := by
  ext x
  rfl

theorem resW_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (X : CMExt E Ω) (Y : CMExt X.M Ω) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {w' : HeightOneSpectrum (𝓞 X.M)} {w'' : HeightOneSpectrum (𝓞 (cmComp X Y).M)}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (h'' : IsPlaceOver A w'') :
    resW (E' := (cmComp X Y).M) h h'' = (resW h h').comp (resW (E := X.M) (E' := Y.M) h' h'') :=
  MonoidHom.ext fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem isLift_comp (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 1 ≤ a) {X : CMExt E Ω} {Y : CMExt X.M Ω}
    {π : CuspSub E a} {P : CuspSub X.M a} {P₂ : CuspSub Y.M a}
    (h₁ : IsLift Ω X π P) (h₂ : IsLift Ω Y P P₂) : IsLift Ω (cmComp X Y) π P₂ := by
  refine ⟨h₂.csd, h₂.reg, ?_⟩
  intro l _ ι r wt HT r₂ wt₂ HT₂ hr hr₂
  obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha h₁.reg h₁.csd
  obtain ⟨p₁, hp₁⟩ := h₁.res l ι r wt HT r₁ wt₁ HT₁ hr hr₁
  obtain ⟨p₂, hp₂⟩ := h₂.res l ι r₁ wt₁ HT₁ r₂ wt₂ HT₂ hr₁ hr₂
  refine ⟨p₂ * p₁, fun g => ?_⟩
  rw [hp₂ g, hp₁, resG_comp X Y g]
  simp only [mul_inv_rev, mul_assoc]

end CMCompositionLift

open CMCompositionLift in
theorem cm_composition_lift_holds : WeakLiftRestriction := by
  intro hG hFS hFSp hK2c hK3a hT E Ω _ _ _ _ _ _ a ha π hc hreg A w h U hU
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  induction hU with
  | top =>
    obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι ha hreg hc
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a E Ω 2 a ha r hr.cont
    obtain ⟨H, hgood, hHN, hDec, hsp⟩ := hFSp E Ω A w h N hN hNo
    obtain ⟨X, P, hXr, hXl⟩ := hT E Ω a ha π hc hreg 2 ι r wt HT hr H hgood (hTr H hHN)
    obtain ⟨w', h', -, -, hW⟩ := hK2c E Ω A w h X
    refine ⟨X, P, w', h', ?_, hsp X hXr w' h', hXl⟩
    rw [eq_top_iff]
    intro σ _
    rw [hW, hXr]
    obtain ⟨a', b', hσ⟩ := σ.2
    exact hDec hσ.1
  | @step U V _ hVU hn hp hs ih =>
    obtain ⟨X, P, w', h', hXr, hsp, hXl⟩ := ih
    obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha hXl.reg hXl.csd
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a X.M Ω 2 a ha r₁ hr₁.cont
    have hVn : (V.comap (resW h h')).Normal := ⟨fun n hn0 g => by
      have hn0' : resW h h' n ∈ V := hn0
      have hgU : resW h h' g ∈ U := by rw [← hXr]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
      have key := hn.conj_mem (⟨resW h h' n, hVU hn0'⟩ : U) (Subgroup.mem_subgroupOf.mpr hn0')
        (⟨resW h h' g, hgU⟩ : U)
      rw [Subgroup.mem_subgroupOf] at key
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      simpa using key⟩
    have hVi : (V.comap (resW h h')).index.Prime := by
      rw [Subgroup.index_comap, hXr]; exact hp
    have hVs : SmoothSub (V.comap (resW h h')) := by
      obtain ⟨O, hO, hOV⟩ := hs
      refine ⟨O.comap (resG E), continuous_resG.isOpen_preimage (O : Set (G E Ω)) hO, fun σ hσ hσO => ?_⟩
      rw [Subgroup.mem_comap]
      apply hOV
      · rw [deg_resW, hσ, mul_zero]
      · exact hσO
    obtain ⟨H, hgood, hHN, hiff⟩ := hFS X.M Ω A w' h' hsp (V.comap (resW h h')) hVn hVi hVs N hN hNo
    obtain ⟨Y, P₂, hYr, hYl⟩ := hT X.M Ω a ha P hXl.csd hXl.reg 2 ι r₁ wt₁ HT₁ hr₁ H hgood (hTr H hHN)
    obtain ⟨w'', h'', hsp', -, hW⟩ := hK2c X.M Ω A w' h' Y
    have hR : (resW h' h'').range = V.comap (resW h h') := by
      ext σ
      rw [hW, hYr, hiff]
    refine ⟨cmComp X Y, P₂, w'', h'', ?_, hsp' hsp, isLift_comp hG ha hXl hYl⟩
    rw [resW_comp X Y h h' h'', MonoidHom.range_comp, hR, Subgroup.map_comap_eq, hXr, inf_of_le_right hVU]

end PositivityTheory.Pf1.CLGD.K

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.FontaineRestriction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Pst

namespace PositivityTheory.Pf1.CLGD.K.FontaineRestriction

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

theorem wdRes_eq {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') :
    PositivityTheory.Pf1.CLGD.DescRes.WD.res h h' = PositivityTheory.Pf1.CLGD.WdRestrict.WD.res h h' := rfl

theorem exists_resBridge {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) :
    ∃ (LL : FinExt l) (Bw' : LocBridge l E' Ω (Dec (F := E') A) ↥(OL LL)),
      Induces Bw' ∧ PositivityTheory.Pf1.CLGD.WdRestrict.IsResBridge Bw Bw' := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := Formalism.BasicNotions.Examples₂.LB.isAlgClosureQ E' Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hA : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1 := hj
  haveI := Formalism.BasicNotions.Examples₂.LB.KwF_fin (E := E') Bw.j
  refine ⟨Formalism.BasicNotions.Examples₂.LB.nclo (Formalism.BasicNotions.Examples₂.LB.KwF (E := E') Bw.j),
    Formalism.BasicNotions.Examples₂.LB.bridgeOf (E := E') hA _ (Formalism.BasicNotions.Examples₂.LB.mem_nclo _), hA, fun g => ?_⟩
  refine congrArg (fun τ => τ) (GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding Bw.j)
    fun x => ?_)
  exact (Formalism.BasicNotions.Examples₂.LB.eDec_comm hA g x).trans
    (Bw.e_comm (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A g) x).symm

end PositivityTheory.Pf1.CLGD.K.FontaineRestriction

namespace PositivityTheory.Pf1.CLGD.K

theorem fontaine_weil_deligne_restriction : K6 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ P AI _ A w h w' h' O _ _ _ Bw hj hp
  obtain ⟨LL, Bw', hj', hc⟩ := FontaineRestriction.exists_resBridge (E' := X.M) Bw hj
  have e1 : (r.comp (Dec (F := E) A).subtype).comp (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A) =
      (r.comp (PositivityTheory.Pf1.CLGD.DescRes.resG E (E' := X.M))).comp (Dec (F := X.M) A).subtype :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨h1, h2⟩ := PositivityTheory.Pf1.CLGD.WdRestrict.wdAt_res P ι Bw Bw' h h' hj hj' hc _ hp
  rw [e1] at h1 h2
  exact ⟨↥(OL LL), inferInstance, inferInstance, inferInstance, Bw', hj', h1,
    h2.trans (congrFun (FontaineRestriction.wdRes_eq h h').symm _)⟩

end PositivityTheory.Pf1.CLGD.K
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.SupremumMembership
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace PositivityTheory.Pf1.CLGD.K

namespace SupremumMembership

theorem exists_mem_of_sup {Γ : Type*} [Group Γ] (H N : Subgroup Γ) [N.Normal] (hHN : H ⊔ N = ⊤)
    (H₁ H₂ : Subgroup Γ) (h1 : H ≤ H₁) (h12 : H₁ < H₂) : ∃ n ∈ H₂, n ∉ H₁ ∧ n ∈ N := by
  obtain ⟨g, hg2, hg1⟩ := SetLike.exists_of_lt h12
  have hg : g ∈ ((H ⊔ N : Subgroup Γ) : Set Γ) := by rw [hHN]; exact Subgroup.mem_top g
  rw [Subgroup.mul_normal H N] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hg
  have hx1 : x ∈ H₁ := h1 hx
  refine ⟨y, ?_, ?_, hy⟩
  · have : y = x⁻¹ * (x * y) := by group
    rw [this]
    exact H₂.mul_mem (H₂.inv_mem (h12.le hx1)) hg2
  · intro hy1
    exact hg1 (H₁.mul_mem hx1 hy1)

end SupremumMembership

open SupremumMembership in
theorem place_membership_of_sup : KillingPolyConst := by
  intro E Ω _ _ _ _ _ l a _ ha r hr
  have hcont : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G E Ω) := {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne.preimage hcont
  have h1U : (1 : G E Ω) ∈ U := by
    show (r 1 : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0
    rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have : N.toSubgroup.Normal := N.isNormal'
  refine ⟨N.toSubgroup, N.isNormal', N.isOpen', fun H hHN H₁ H₂ h1 h12 => ?_⟩
  obtain ⟨n, hn2, hn1, hnN⟩ := exists_mem_of_sup H N.toSubgroup hHN H₁ H₂ h1 h12
  exact ⟨n, hn2, hn1, hN hnN⟩

end PositivityTheory.Pf1.CLGD.K

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.WeilDeligneRestriction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
open GlobalTheory.WeilDeligne PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilDeligneRestriction

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω}

theorem mem_Dec_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Dec (F := E) A) : σ ∈ Dec (F := E') A := by
  have h1 : resG E σ • A = A := hσ
  show σ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

theorem mem_Ine_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Ine (F := E) A) : σ ∈ Ine (F := E') A :=
  ⟨mem_Dec_of_resG hσ.1, fun x hx => hσ.2 x hx⟩

variable (E A) in

def resIne : Ine (F := E') A →* Ine (F := E) A where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

@[simp] theorem coe_resIne (σ : Ine (F := E') A) : ((resIne E A σ : Ine (F := E) A) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

theorem continuous_resIne : Continuous (resIne E A : Ine (F := E') A → Ine (F := E) A) := by
  show Continuous fun σ : Ine (F := E') A => (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : Ine (F := E) A)
  exact ((continuous_resG (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val).subtype_mk _

theorem exists_tval_resIne_ne {l : ℕ} [Fact l.Prime] {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t) :
    ∃ σ : Ine (F := E') A, tval t (resIne E A σ) ≠ 0 := by
  classical
  let bQ := Module.finBasis ℚ E'
  let K : IntermediateField E Ω := IntermediateField.adjoin E (Set.range fun i => algebraMap E' Ω (bQ i))
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let U : Subgroup (Ine (F := E) A) := K.fixingSubgroup.comap (Ine (F := E) A).subtype
  have hU : IsOpen (U : Set (Ine (F := E) A)) :=
    (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val
  obtain ⟨σ, hσ, hne⟩ := ht.exists_tval_ne_zero hU
  have hσ' : (σ : G E Ω) ∈ K.fixingSubgroup := hσ
  have hb : ∀ i, (σ : G E Ω) (algebraMap E' Ω (bQ i)) = algebraMap E' Ω (bQ i) := fun i =>
    (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have : CharZero Ω := (RingHom.charZero_iff (algebraMap E Ω).injective).mp inferInstance
  have hfix : ∀ y : E', (σ : G E Ω) (algebraMap E' Ω y) = algebraMap E' Ω y := by
    intro y
    rw [← bQ.sum_repr y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_rat_smul, map_rat_smul, hb]
  let τ : G E' Ω := { (σ : G E Ω).toRingEquiv with commutes' := hfix }
  have hτ : resG E τ = (σ : G E Ω) := AlgEquiv.ext fun _ => rfl
  have hτI : τ ∈ Ine (F := E') A := mem_Ine_of_resG (by rw [hτ]; exact σ.2)
  refine ⟨⟨τ, hτI⟩, ?_⟩
  have e : resIne E A ⟨τ, hτI⟩ = σ := Subtype.ext hτ
  rw [e]
  exact hne

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

include h h' in

theorem notMem_of_place (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal := by
  intro H
  apply hl
  rw [← h]
  have := (h' _).mpr H
  simpa using this

theorem exists_conj_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hl' : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {t' : Ine (F := E') A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') {r : G E Ω →* GL n (Qbar l)} {N : Matrix n n (Qbar l)}
    (hN : IsMonodromy t r N) {φ : Weil h} (hφ : deg φ = 1) {φ' : Weil h'} (hφ' : deg φ' = 1) {c' : Qbar l}
    (hct : ∀ σ, tval t (resIne E A σ) = c' * tval t' σ) :
    ∃ b : Qbar l, ∀ g, exp (b • N) * wdMat t hφ r N (resW h h' g) =
      wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g * exp (b • N) := by
  have hpow : ∀ g : Weil h', ((normV w : ℕ) : Qbar l) ^ deg (resW h h' g) = ((normV w' : ℕ) : Qbar l) ^ deg g :=
    fun g => by rw [deg_resW, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow_resF h h']
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq1 : 1 - ((normV w' : ℕ) : Qbar l)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    exact Nat.cast_ne_one.mpr (one_lt_normV w').ne'
  let D : Weil h' → Qbar l := fun g => c' * tval t' (inePart hφ' g) - tval t (inePart hφ (resW h h' g))
  have hD : ∀ g g', D (g * g') = (((normV w' : ℕ) : Qbar l) ^ deg g')⁻¹ * D g + D g' := fun g g' => by
    simp only [D, map_mul, ht'.tval_inePart_mul hl' hφ', ht.tval_inePart_mul hl hφ, hpow]
    ring
  have hD0 : ∀ g, deg g = 0 → D g = 0 := fun g hg => by
    have e : g = ineIncl h' ⟨g, deg_eq_zero_iff.mp hg⟩ := rfl
    have e2 : ∀ σ : Ine (F := E') A, resW h h' (ineIncl h' σ) = ineIncl h (resIne E A σ) := fun σ => Subtype.ext rfl
    rw [e]
    simp only [D, e2, inePart_ineIncl, hct, sub_self]
  obtain ⟨b, hb⟩ : ∃ b : Qbar l, b = D φ' / (1 - ((normV w' : ℕ) : Qbar l)⁻¹) := ⟨_, rfl⟩
  have key : ∀ g, D g = (1 - (((normV w' : ℕ) : Qbar l) ^ deg g)⁻¹) * b := fun g => by
    have h1 := hD (φ' * g) ((φ' * g)⁻¹ * (g * φ'))
    have h0 : deg ((φ' * g)⁻¹ * (g * φ')) = 0 := by simp only [deg_mul, deg_inv]; ring
    rw [mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ', zpow_one, zpow_zero, inv_one, one_mul,
      add_zero] at h1
    rw [hb, ← mul_div_assoc, eq_div_iff hq1]
    linear_combination -h1
  refine ⟨b, fun g => ?_⟩
  have h2 := hN.mul_exp hl ht (resW h h' g) ((((normV w : ℕ) : Qbar l) ^ deg (resW h h' g))⁻¹ * b)
  rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)] at h2
  have hw : wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g =
      (r (resW h h' g) : Matrix n n (Qbar l)) * exp ((-(c' * tval t' (inePart hφ' g))) • N) := by
    rw [wdMat, smul_smul, show -tval t' (inePart hφ' g) * c' = -(c' * tval t' (inePart hφ' g)) by ring]
    rfl
  rw [hw, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have k := key g
  simp only [D] at k
  rw [hpow]
  linear_combination k

theorem isWDOf_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) {x : WD h}
    (hx : IsWDOf ι r x) : IsWDOf ι (r.comp (resG E (E' := E') (Ω := Ω))) (WD.res h h' x) := by
  obtain ⟨t, ht, φ, hφ, N, a0, hN, ha, rfl⟩ := hx
  have hl' := notMem_of_place h h' hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul E' Ω A w' h' l hl' (t.comp (resIne E A)) (tameL h' hl')
    (ht.1.comp continuous_resIne) ht'.1 ht'.2
  have hct : ∀ σ, tval t (resIne E A σ) = algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) * tval (tameL h' hl') σ := fun σ => by
    have e : (t (resIne E A σ)).toAdd = c * ((tameL h' hl') σ).toAdd := hc σ
    simp only [tval, e, PadicInt.coe_mul, map_mul]
  generalize algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) = c' at hct
  have hc0 : c' ≠ 0 := by
    intro h0
    obtain ⟨σ, hσ⟩ := exists_tval_resIne_ne (E' := E') ht
    exact hσ (by rw [hct, h0, zero_mul])
  have hN' : IsMonodromy (tameL h' hl') (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) := by
    obtain ⟨U, hU, H⟩ := hN.2
    refine ⟨hN.1.smul c', U.comap (resIne E A), hU.preimage continuous_resIne, fun σ hσ => ?_⟩
    rw [smul_smul, mul_comm (tval _ σ), ← hct]
    exact H _ hσ
  have hφ' : deg (frob h') = 1 := deg_frob
  obtain ⟨bb, hbb⟩ := exists_conj_res h h' hl hl' ht ht' hN hφ hφ' hct
  obtain ⟨b', hb'⟩ := hN'.exists_isFrobSS hl' ht' hφ' ι
  refine ⟨tameL h' hl', ht', frob h', hφ', c' • N, b', hN', hb', ?_⟩
  rw [WD.res_mk]
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul bb)).map (toEndC ι)
  have ha2 : IsFrobSS (fun g => toEndC ι (wdMat t hφ r N (resW h h' g))) (toEndC ι N) (resRep h h' a0) :=
    ⟨ha.1, fun g => ha.2 (resW h h' g)⟩
  have hcomm : ∀ g, (hN'.rep hl' ht' hφ' ι) g * toEndC ι N =
      ((normV w' : ℕ) : ℂ) ^ deg g • (toEndC ι N * (hN'.rep hl' ht' hφ' ι) g) := fun g => by
    have H := hN'.rep_comm hl' ht' hφ' ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at H
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) H
  obtain ⟨b1, hb1⟩ := exists_isFrobSS (hN'.rep hl' ht' hφ' ι) (toEndC ι N) (hN'.isSmooth_rep hl' ht' hφ' ι)
    (hN.1.map (toEndC ι)) hcomm
  have i1 : (resRep h h' a0).Iso b1 := ha2.iso hb1 (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N (resW h h' g))) v =
        (toEndC ι (wdMat (tameL h' hl') hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g) *
          (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, hbb, map_mul])
    (fun v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : b1.Iso b' := IsFrobSS.iso_of_smul ((map_ne_zero ι).mpr hc0) hb1 (by rw [← toEndC_smul]; exact hb')
  exact WD.sound (i1.trans i2).symm

end

end WeilDeligneRestriction

theorem weil_deligne_restriction_away : K5 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ A w h w' h' hl x hx
  exact WeilDeligneRestriction.isWDOf_res h h' hl ι r hx

end PositivityTheory.Pf1.CLGD.K

end
end

